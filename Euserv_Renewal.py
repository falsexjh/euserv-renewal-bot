# SPDX-License-Identifier: GPL-3.0-or-later
# Inspired by https://github.com/zensea/AutoEUServerlessWith2FA and https://github.com/WizisCool/AutoEUServerless

import os
import re
import time
import base64
import hmac
import struct
import ast
import operator
import requests
import imaplib
import email
import smtplib

from enum import Enum
from datetime import date, datetime
from bs4 import BeautifulSoup
from email.mime.text import MIMEText

# ==================== 自定义异常 ====================

class CaptchaError(Exception):
    """验证码处理相关错误"""
    pass

class PinRetrievalError(Exception):
    """PIN码获取相关错误"""
    pass

class LoginError(Exception):
    """登录相关错误"""
    pass

class RenewalError(Exception):
    """续期相关错误"""
    pass

# ==================== 环境变量配置 ====================

EUSERV_USERNAME = os.getenv('EUSERV_USERNAME')
EUSERV_PASSWORD = os.getenv('EUSERV_PASSWORD')
EUSERV_2FA = os.getenv('EUSERV_2FA')

CAPTCHA_USERID = os.getenv('CAPTCHA_USERID')
CAPTCHA_APIKEY = os.getenv('CAPTCHA_APIKEY')

EMAIL_HOST = os.getenv('EMAIL_HOST')
EMAIL_USERNAME = os.getenv('EMAIL_USERNAME')
EMAIL_PASSWORD = os.getenv('EMAIL_PASSWORD')
NOTIFICATION_EMAIL = os.getenv('NOTIFICATION_EMAIL')

# SMTP 配置 (可选)
SMTP_HOST = os.getenv('SMTP_HOST') or (EMAIL_HOST.replace("imap", "smtp") if EMAIL_HOST else None)
_smtp_port_env = os.getenv('SMTP_PORT')
SMTP_PORT = int(_smtp_port_env) if _smtp_port_env and _smtp_port_env.strip() else 587

# GitHub Actions 输出
GITHUB_OUTPUT = os.getenv('GITHUB_OUTPUT')

# 常量定义
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/95.0.4638.69 Safari/537.36"
)

# 时间配置 (秒)
LOGIN_MAX_RETRY_COUNT = 3
HTTP_TIMEOUT_SECONDS = 30
RETRY_DELAY_SECONDS = 5
API_TIMEOUT_SECONDS = 20
EMAIL_CHECK_INTERVAL = 10
EMAIL_MAX_RETRIES = 3

# 退出码
EXIT_SUCCESS = 0  # 成功或无需操作
EXIT_FAILURE = 1  # 失败
EXIT_SKIPPED = 2  # 跳过

# 字符串匹配常量
CAPTCHA_PROMPT = "To finish the login process please solve the following captcha."
TWO_FA_PROMPT = "To finish the login process enter the PIN that is shown in yout authenticator app."
TWO_FA_PROMPT2 = "To finish the login process enter the PIN that you receive via email."
LOGIN_SUCCESS_INDICATORS = ("Hello", "Confirm or change your customer data here")
RENEWAL_DATE_PATTERN = r"Contract extension possible from"

# URL 常量
EUSERV_BASE_URL = "https://support.euserv.com/index.iphp"
EUSERV_CAPTCHA_URL = "https://support.euserv.com/securimage_show.php"
TRUECAPTCHA_API_URL = "https://api.apitruecaptcha.org/one/gettext"


class LogLevel(Enum):
    """日志级别与对应的 Emoji 图标"""
    INFO = "ℹ️"
    SUCCESS = "✅"
    WARNING = "⚠️"
    ERROR = "❌"
    PROGRESS = "🔄"
    CELEBRATION = "🎉"


# ==================== 辅助工具函数 ====================

def _hotp(key: str, counter: int, digits: int = 6, digest: str = 'sha1') -> str:
    """HOTP 算法实现"""
    key_bytes = base64.b32decode(key.upper() + '=' * ((8 - len(key)) % 8))
    counter_bytes = struct.pack('>Q', counter)
    mac = hmac.new(key_bytes, counter_bytes, digest).digest()
    offset = mac[-1] & 0x0f
    binary = struct.unpack('>L', mac[offset:offset + 4])[0] & 0x7fffffff
    return str(binary)[-digits:].zfill(digits)


def _totp(key: str, time_step: int = 30, digits: int = 6, digest: str = 'sha1') -> str:
    """TOTP 算法实现"""
    return _hotp(key, int(time.time() / time_step), digits, digest)


def _safe_eval_math(expr: str) -> int | None:
    """安全计算简单数学表达式 (仅支持 +, -, *, /)"""
    ops = {
        ast.Add: operator.add,
        ast.Sub: operator.sub,
        ast.Mult: operator.mul,
        ast.Div: operator.floordiv
    }

    def _eval(node):
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.BinOp) and type(node.op) in ops:
            return ops[type(node.op)](_eval(node.left), _eval(node.right))
        raise ValueError("Unsupported expression")

    try:
        return int(_eval(ast.parse(expr, mode='eval').body))
    except (SyntaxError, ValueError, TypeError, ZeroDivisionError):
        return None


class RenewalBot:
    """
    Euserv VPS 自动续期机器人类。
    封装了所有业务逻辑和状态，提供更好的可测试性和可维护性。
    """

    def __init__(self):
        self.log_messages: list[str] = []
        self.current_login_attempt = 1
        self.session: requests.Session | None = None
        self.sess_id: str | None = None
        self._ocr = None  # OCR 实例懒加载

    def _cleanup(self) -> None:
        """清理资源，关闭 HTTP Session"""
        if self.session:
            self.session.close()
            self.session = None

    # ==================== 日志系统 ====================

    def log(self, info: str, level: LogLevel = LogLevel.INFO) -> None:
        """记录日志消息到实例日志列表，带时间戳。"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        
        # 如果是普通 INFO，只显示文字；否则显示 Emoji + 文字
        content = f"{level.value} {info}" if level != LogLevel.INFO else info
        formatted_line = f"[{timestamp}] {content}"

        print(formatted_line)
        self.log_messages.append(formatted_line)

    # ==================== 邮件与配置 ====================

    def validate_config(self) -> tuple[bool, list[str]]:
        """验证必需配置，返回 (是否通过, 缺失项列表)。"""
        required = {
            "EUSERV_USERNAME": EUSERV_USERNAME,
            "EUSERV_PASSWORD": EUSERV_PASSWORD,
            "EMAIL_HOST": EMAIL_HOST,
            "EMAIL_USERNAME": EMAIL_USERNAME,
            "EMAIL_PASSWORD": EMAIL_PASSWORD,
        }
        missing = [k for k, v in required.items() if not v]
        return len(missing) == 0, missing

    def send_status_email(self, subject_status: str) -> None:
        """发送状态通知邮件。"""
        if not (NOTIFICATION_EMAIL and EMAIL_USERNAME and EMAIL_PASSWORD):
            self.log("邮件通知配置不完整，跳过发送。", LogLevel.WARNING)
            return
        if not SMTP_HOST:
            self.log("无法推断 SMTP 服务器地址，跳过发送。", LogLevel.WARNING)
            return

        self.log("正在准备发送状态通知邮件...")
        sender = EMAIL_USERNAME
        recipient = NOTIFICATION_EMAIL
        subject = f"Euserv 续约脚本运行报告 - {subject_status}"
        body = "Euserv 自动续约脚本本次运行的详细日志如下：\n\n" + "\n".join(self.log_messages)
        
        msg = MIMEText(body, 'plain', 'utf-8')
        msg['Subject'] = subject
        msg['From'] = sender
        msg['To'] = recipient

        try:
            server = smtplib.SMTP(SMTP_HOST, SMTP_PORT)
            server.starttls()
            server.login(EMAIL_USERNAME, EMAIL_PASSWORD)
            server.sendmail(sender, [recipient], msg.as_string())
            server.quit()
            self.log("状态通知邮件已成功发送！", LogLevel.CELEBRATION)
        except smtplib.SMTPException as e:
            self.log(f"发送邮件失败: {e}", LogLevel.ERROR)

    # ==================== OCR 识别 ====================

    def _get_ocr(self):
        """获取或创建 OCR 实例（懒加载单例）"""
        if self._ocr is None:
            import ddddocr
            self._ocr = ddddocr.DdddOcr(show_ad=False)
        return self._ocr

    def prewarm_ocr(self) -> None:
        """预加载 OCR 模型"""
        self.log("正在预加载 OCR 模型...", LogLevel.PROGRESS)
        try:
            self._get_ocr()
            self.log("OCR 模型预加载完成", LogLevel.SUCCESS)
        except Exception as e:
            self.log(f"OCR 预加载失败 (将在需要时重试): {e}", LogLevel.WARNING)

    def _solve_captcha_local(self, image_bytes: bytes) -> str | None:
        """使用本地 ddddocr 识别"""
        ocr = self._get_ocr()
        captcha_text = ocr.classification(image_bytes)

        if not captcha_text:
            return None

        # 尝试数学计算
        math_text = captcha_text.replace('x', '*').replace('X', '*').replace('=', '').strip()
        cleaned = ''.join(c for c in math_text if c in '0123456789+-*/')

        if cleaned and any(op in cleaned for op in ['+', '-', '*', '/']):
            result = _safe_eval_math(cleaned)
            if result is not None:
                return str(result)

        return captcha_text

    def _solve_captcha_api(self, image_bytes: bytes) -> str | None:
        """使用 TrueCaptcha API 识别"""
        encoded_string = base64.b64encode(image_bytes).decode('ascii')
        data = {
            'userid': CAPTCHA_USERID,
            'apikey': CAPTCHA_APIKEY,
            'data': encoded_string
        }

        max_retries = 3
        for attempt in range(max_retries):
            try:
                resp = requests.post(url=TRUECAPTCHA_API_URL, json=data, timeout=API_TIMEOUT_SECONDS)
                resp.raise_for_status()
                result_data = resp.json()

                if result_data.get('status') == 'error':
                    self.log(f"API返回错误: {result_data.get('message')}", LogLevel.WARNING)
                    return None

                captcha_text = result_data.get('result')
                if captcha_text:
                    math_expr = captcha_text.replace('x', '*').replace('X', '*')
                    result = _safe_eval_math(math_expr)
                    return str(result) if result is not None else captcha_text

            except requests.RequestException as e:
                self.log(f"API请求失败 (尝试 {attempt + 1}/{max_retries}): {e}", LogLevel.WARNING)
                if attempt < max_retries - 1:
                    time.sleep(RETRY_DELAY_SECONDS)

        return None

    def _solve_captcha(self, image_bytes: bytes) -> str:
        """验证码识别策略：本地优先，多次失败后尝试 API"""
        # 失败多次后强制使用 API
        if self.current_login_attempt >= 3 and CAPTCHA_USERID and CAPTCHA_APIKEY:
            self.log(f"第 {self.current_login_attempt} 次尝试，切换至 TrueCaptcha API...", LogLevel.WARNING)
            result = self._solve_captcha_api(image_bytes)
            if result:
                self.log(f"API 识别结果: {result}", LogLevel.SUCCESS)
                return result

        # 优先本地 OCR
        self.log("使用本地 OCR (ddddocr) 识别...")
        try:
            result = self._solve_captcha_local(image_bytes)
            if result:
                self.log(f"本地 OCR 识别结果: {result}", LogLevel.SUCCESS)
                return result
        except Exception as e:
            self.log(f"本地 OCR 识别报错: {e}", LogLevel.WARNING)

        # 本地失败兜底 API
        self.log("本地 OCR 失败，尝试 TrueCaptcha API...", LogLevel.PROGRESS)
        if CAPTCHA_USERID and CAPTCHA_APIKEY:
            result = self._solve_captcha_api(image_bytes)
            if result:
                self.log(f"API 识别结果: {result}", LogLevel.SUCCESS)
                return result
            raise CaptchaError("TrueCaptcha API 也无法识别")
        else:
            raise CaptchaError("本地 OCR 失败且未配置 API")

    # ==================== 登录验证处理 ====================

    def _handle_captcha(self, url: str, captcha_image_url: str, headers: dict,
                        sess_id: str, username: str, password: str) -> requests.Response | None:
        """处理图片验证码"""
        self.log("检测到图片验证码，正在处理...", LogLevel.PROGRESS)
        image_resp = self.session.get(captcha_image_url, headers={'user-agent': USER_AGENT},
                                      timeout=HTTP_TIMEOUT_SECONDS)
        image_resp.raise_for_status()
        image_bytes = image_resp.content

        captcha_code = self._solve_captcha(image_bytes)
        
        post_data = {
            "email": username,
            "password": password,
            "subaction": "login",
            "sess_id": sess_id,
            "captcha_code": str(captcha_code)
        }
        resp = self.session.post(url, headers=headers, data=post_data, timeout=HTTP_TIMEOUT_SECONDS)

        if CAPTCHA_PROMPT in resp.text:
            self.log("图片验证码验证失败", LogLevel.ERROR)
            try:
                with open('captcha_failed.png', 'wb') as f:
                    f.write(image_bytes)
                self.log(f"验证码图片已保存至 captcha_failed.png，识别值: {captcha_code}")
            except OSError:
                pass
            return None
            
        self.log("图片验证码验证通过", LogLevel.SUCCESS)
        return resp

    def _handle_2fa_email(self, url: str, headers: dict, response_text: str) -> requests.Response | None:
        """处理邮箱 PIN 验证"""
        self.log("检测到邮箱 PIN 二次验证", LogLevel.PROGRESS)

        try:
            pin = self._get_pin_from_gmail()
            self.log(f"成功获取邮箱 PIN: {pin}", LogLevel.SUCCESS)
        except PinRetrievalError as e:
            self.log(f"获取邮箱 PIN 失败: {e}", LogLevel.ERROR)
            return None

        soup = BeautifulSoup(response_text, "html.parser")
        hidden_inputs = soup.find_all("input", type="hidden")
        two_fa_data = {inp.get("name"): inp.get("value", "") for inp in hidden_inputs if inp.get("name")}
        two_fa_data["pin"] = pin

        resp = self.session.post(url, headers=headers, data=two_fa_data, timeout=HTTP_TIMEOUT_SECONDS)

        if "Error: This PIN is invalid." in resp.text:
            self.log("邮箱 PIN 验证失败", LogLevel.ERROR)
            return None

        self.log("邮箱 PIN 验证通过", LogLevel.SUCCESS)
        return resp

    def _handle_2fa(self, url: str, headers: dict, response_text: str) -> requests.Response | None:
        """处理 TOTP 2FA 验证"""
        self.log("检测到 TOTP 2FA 验证", LogLevel.PROGRESS)
        if not EUSERV_2FA:
            self.log("未配置 EUSERV_2FA，无法登录。", LogLevel.ERROR)
            return None

        two_fa_code = _totp(EUSERV_2FA)
        self.log(f"生成 2FA 代码: {two_fa_code}")

        soup = BeautifulSoup(response_text, "html.parser")
        hidden_inputs = soup.find_all("input", type="hidden")
        two_fa_data = {inp["name"]: inp.get("value", "") for inp in hidden_inputs}
        two_fa_data["pin"] = two_fa_code

        resp = self.session.post(url, headers=headers, data=two_fa_data, timeout=HTTP_TIMEOUT_SECONDS)
        
        if TWO_FA_PROMPT in resp.text:
            self.log("2FA 验证失败", LogLevel.ERROR)
            return None
            
        self.log("2FA 验证通过", LogLevel.SUCCESS)
        return resp

    def _perform_login(self) -> tuple[str, requests.Session]:
        """执行登录流程（含重试）"""
        headers = {"user-agent": USER_AGENT, "origin": "https://www.euserv.com"}
        self.session = requests.Session()

        for attempt in range(LOGIN_MAX_RETRY_COUNT):
            self.current_login_attempt = attempt + 1
            if attempt > 0:
                self.log(f"登录尝试 {attempt + 1}/{LOGIN_MAX_RETRY_COUNT} ...", LogLevel.PROGRESS)
                time.sleep(RETRY_DELAY_SECONDS)

            try:
                result = self._attempt_login(headers)
                if result:
                    return result
            except (requests.RequestException, ValueError) as e:
                self.log(f"登录请求异常: {e}", LogLevel.WARNING)

        raise LoginError("登录失败次数过多，退出。")

    def _attempt_login(self, headers: dict) -> tuple[str, requests.Session] | None:
        """单次登录逻辑"""
        # 初始化 Session
        sess_resp = self.session.get(EUSERV_BASE_URL, headers=headers, timeout=HTTP_TIMEOUT_SECONDS)
        sess_resp.raise_for_status()
        sess_id = sess_resp.cookies.get('PHPSESSID')
        if not sess_id:
            raise ValueError("无法获取 PHPSESSID")

        self.session.get("https://support.euserv.com/pic/logo_small.png", headers=headers, timeout=HTTP_TIMEOUT_SECONDS)

        # 提交账号密码
        login_data = {
            "email": EUSERV_USERNAME, "password": EUSERV_PASSWORD, "form_selected_language": "en",
            "Submit": "Login", "subaction": "login", "sess_id": sess_id,
        }
        resp = self.session.post(EUSERV_BASE_URL, headers=headers, data=login_data, timeout=HTTP_TIMEOUT_SECONDS)
        resp.raise_for_status()

        if self._is_login_success(resp.text):
            self.log("登录成功", LogLevel.SUCCESS)
            self.sess_id = sess_id
            return sess_id, self.session

        # 验证码挑战
        if CAPTCHA_PROMPT in resp.text:
            resp = self._handle_captcha(EUSERV_BASE_URL, EUSERV_CAPTCHA_URL, headers, sess_id, EUSERV_USERNAME, EUSERV_PASSWORD)
            if resp is None: return None

        # 2FA 挑战
        if TWO_FA_PROMPT2 in resp.text:
            resp = self._handle_2fa_email(EUSERV_BASE_URL, headers, resp.text)
            if resp is None: return None
        elif TWO_FA_PROMPT in resp.text:
            resp = self._handle_2fa(EUSERV_BASE_URL, headers, resp.text)
            if resp is None: return None

        if self._is_login_success(resp.text):
            self.log("登录成功", LogLevel.SUCCESS)
            self.sess_id = sess_id
            return sess_id, self.session

        self.log("登录失败：所有验证通过后仍未检测到成功标志。", LogLevel.ERROR)
        return None

    @staticmethod
    def _is_login_success(response_text: str) -> bool:
        return any(indicator in response_text for indicator in LOGIN_SUCCESS_INDICATORS)

    # ==================== PIN 码获取 ====================

    @staticmethod
    def _extract_email_body(msg: email.message.Message) -> str:
        if msg.is_multipart():
            for part in msg.walk():
                if part.get_content_type() == "text/plain":
                    return part.get_payload(decode=True).decode()
            return ""
        return msg.get_payload(decode=True).decode()

    def _fetch_pin_from_email(self, mail: imaplib.IMAP4_SSL, search_criteria: str) -> str | None:
        status, messages = mail.search(None, search_criteria)
        if status != 'OK' or not messages[0]:
            return None

        latest_email_id = messages[0].split()[-1]
        _, data = mail.fetch(latest_email_id, '(RFC822)')
        raw_email = data[0][1].decode('utf-8')
        msg = email.message_from_string(raw_email)
        body = self._extract_email_body(msg)

        pin_match = re.search(r"PIN:\s*\n?(\d{6})", body, re.IGNORECASE)
        return pin_match.group(1) if pin_match else None

    def _get_pin_from_gmail(self) -> str:
        self.log("连接 Gmail 获取 PIN 码...", LogLevel.PROGRESS)
        today_str = date.today().strftime('%d-%b-%Y')
        search_criteria = f'(SINCE "{today_str}" FROM "no-reply@euserv.com" SUBJECT "EUserv - ")'
        
        time.sleep(EMAIL_CHECK_INTERVAL)
        
        for i in range(EMAIL_MAX_RETRIES):
            try:
                with imaplib.IMAP4_SSL(EMAIL_HOST) as mail:
                    mail.login(EMAIL_USERNAME, EMAIL_PASSWORD)
                    mail.select('inbox')
                    pin = self._fetch_pin_from_email(mail, search_criteria)
                    if pin:
                        return pin
                self.log(f"第 {i + 1} 次尝试未找到邮件，重试中...", LogLevel.PROGRESS)
                time.sleep(EMAIL_CHECK_INTERVAL)
            except (imaplib.IMAP4.error, OSError) as e:
                self.log(f"IMAP 连接错误: {e}", LogLevel.ERROR)
                raise PinRetrievalError(f"邮件连接错误: {e}") from e
                
        raise PinRetrievalError("多次尝试后仍无法获取 PIN。")

    # ==================== 业务逻辑：获取与续期 ====================

    def _get_servers(self) -> list[dict]:
        """获取服务器列表状态"""
        self.log("正在拉取服务器列表...", LogLevel.PROGRESS)
        server_list = []
        url = f"{EUSERV_BASE_URL}?sess_id={self.sess_id}"
        headers = {"user-agent": USER_AGENT}
        
        resp = self.session.get(url=url, headers=headers, timeout=HTTP_TIMEOUT_SECONDS)
        resp.raise_for_status()
        
        soup = BeautifulSoup(resp.text, "html.parser")
        selector = "#kc2_order_customer_orders_tab_content_1 .kc2_order_table.kc2_content_table tr, #kc2_order_customer_orders_tab_content_2 .kc2_order_table.kc2_content_table tr"
        
        for tr in soup.select(selector):
            server_id_tag = tr.select_one(".td-z1-sp1-kc")
            if not server_id_tag: continue
            
            server_id = server_id_tag.get_text(strip=True)
            action_container = tr.select_one(".td-z1-sp2-kc .kc2_order_action_container")
            
            if action_container:
                action_text = action_container.get_text()
                if RENEWAL_DATE_PATTERN in action_text:
                    match = re.search(r'\d{4}-\d{2}-\d{2}', action_text)
                    renewal_date = match.group(0) if match else "未知日期"
                    server_list.append({"id": server_id, "renewable": False, "date": renewal_date})
                else:
                    server_list.append({"id": server_id, "renewable": True, "date": None})
                    
        return server_list

    def _renew(self, order_id: str) -> bool:
        """执行单台服务器续期"""
        self.log(f"发起续约请求: {order_id}", LogLevel.PROGRESS)
        url = EUSERV_BASE_URL
        headers = {"user-agent": USER_AGENT, "Host": "support.euserv.com", "origin": "https://support.euserv.com"}
        
        # 步骤 1: 选择订单
        data1 = {
            "Submit": "Extend contract", "sess_id": self.sess_id, "ord_no": order_id,
            "subaction": "choose_order", "choose_order_subaction": "show_contract_details",
        }
        self.session.post(url, headers=headers, data=data1, timeout=HTTP_TIMEOUT_SECONDS)
        
        # 步骤 2: 触发密码框
        data2 = {
            "sess_id": self.sess_id, "subaction": "show_kc2_security_password_dialog",
            "prefix": "kc2_customer_contract_details_extend_contract_", "type": "1",
        }
        self.session.post(url, headers=headers, data=data2, timeout=HTTP_TIMEOUT_SECONDS)
        
        # 步骤 3: 获取并提交 PIN
        pin = self._get_pin_from_gmail()
        data3 = {
            "auth": pin, "sess_id": self.sess_id, "subaction": "kc2_security_password_get_token",
            "prefix": "kc2_customer_contract_details_extend_contract_", "type": 1,
            "ident": f"kc2_customer_contract_details_extend_contract_{order_id}",
        }
        resp = self.session.post(url, headers=headers, data=data3, timeout=HTTP_TIMEOUT_SECONDS)
        resp.raise_for_status()
        
        rs_json = resp.json()
        if rs_json.get("rs") != "success":
            raise RenewalError(f"Token 获取失败: {resp.text}")
            
        token = rs_json["token"]["value"]
        self.log("成功获取续约 Token", LogLevel.SUCCESS)
        
        # 步骤 4: 最终确认
        data4 = {
            "sess_id": self.sess_id, "ord_id": order_id,
            "subaction": "kc2_customer_contract_details_extend_contract_term", "token": token,
        }
        final_resp = self.session.post(url, headers=headers, data=data4, timeout=HTTP_TIMEOUT_SECONDS)
        final_resp.raise_for_status()
        
        return True

    def _process_server_renewals(self, servers_to_renew: list) -> bool:
        """批量处理续期任务"""
        ids = [s['id'] for s in servers_to_renew]
        self.log(f"检测到需续期服务器: {ids}", LogLevel.INFO)
        
        all_success = True
        for server in servers_to_renew:
            self.log(f"--- 正在续期服务器 {server['id']} ---", LogLevel.PROGRESS)
            try:
                self._renew(server['id'])
                self.log(f"服务器 {server['id']} 续期请求提交成功", LogLevel.SUCCESS)
            except (RenewalError, requests.RequestException) as e:
                self.log(f"服务器 {server['id']} 续期失败: {e}", LogLevel.ERROR)
                all_success = False
        return all_success

    # ==================== 调度与收尾 ====================

    def _output_next_schedule(self, date_str: str) -> None:
        """更新 GitHub Action 的 Cron 计划"""
        try:
            parts = date_str.split('-')
            if len(parts) == 3:
                _, month, day = parts
                cron_expr = f"0 0 {int(day)} {int(month)} *"
                self.log(f"下次续约日期: {date_str}", LogLevel.INFO)
                self.log(f"设置 Cron: {cron_expr}", LogLevel.PROGRESS)

                with open(GITHUB_OUTPUT, 'a') as f:
                    f.write(f"next_cron={cron_expr}\n")
                    f.write(f"next_date={date_str}\n")
        except (ValueError, OSError) as e:
            self.log(f"解析续约日期失败: {e}", LogLevel.WARNING)

    def _fetch_server_list_with_retry(self) -> list[dict]:
        """
        续期后带重试机制的列表获取。
        等待 Euserv 后端刷新日期（约需 1-3 分钟）。
        """
        max_retries = 5
        retry_interval = 30
        server_list = []

        for i in range(max_retries + 1):
            try:
                server_list = self._get_servers()
            except Exception as e:
                self.log(f"列表获取异常 (尝试 {i + 1}): {e}", LogLevel.WARNING)

            # 只要有任意一个服务器有了具体日期，就视为成功
            has_valid_date = any(s.get('date') and s['date'] != "未知日期" for s in server_list)

            if has_valid_date:
                if i > 0:
                    self.log(f"在第 {i} 次重试后成功获取到续约日期。", LogLevel.SUCCESS)
                return server_list

            if i < max_retries:
                self.log(f"等待页面更新日期... ({i + 1}/{max_retries}, 间隔 {retry_interval}s)", LogLevel.PROGRESS)
                time.sleep(retry_interval)
            else:
                self.log("超时：页面仍未刷新下次续约日期，将使用默认调度。", LogLevel.WARNING)

        return server_list

    def _finalize_report_and_schedule(self, server_list: list[dict]) -> None:
        """
        生成最终报告并计算 Cron 计划。
        统一使用 LogLevel 控制图标，不再手动定义 icon 变量。
        """
        self.log("--- 最终状态报告 ---", LogLevel.INFO)

        earliest_date = None
        all_clear = True

        for server in server_list:
            if server['renewable']:
                # 异常状态：应该续期完了但还是 renewable
                level = LogLevel.WARNING
                status_text = "仍需续期 (操作可能未生效)"
                all_clear = False
            else:
                # 正常状态
                level = LogLevel.SUCCESS
                status_text = "无需续期"

            date_str = server.get('date', '未知日期')
            self.log(f"服务器 {server['id']}: {status_text} | 下次窗口: {date_str}", level)

            # 计算最早日期
            if date_str and date_str != "未知日期":
                if earliest_date is None or date_str < earliest_date:
                    earliest_date = date_str

        if all_clear:
            self.log("所有服务器状态正常。", LogLevel.CELEBRATION)
        else:
            self.log("存在异常状态服务器，请检查。", LogLevel.WARNING)

        # 更新 Cron
        if earliest_date:
            self.log(f"最早续约窗口: {earliest_date}", LogLevel.INFO)
            if GITHUB_OUTPUT:
                self._output_next_schedule(earliest_date)
        else:
            self.log("未能获取有效日期，跳过 Cron 更新。", LogLevel.WARNING)

    def run(self) -> int:
        """主运行逻辑"""
        config_ok, missing = self.validate_config()
        if not config_ok:
            self.log(f"缺少配置: {', '.join(missing)}", LogLevel.ERROR)
            return EXIT_FAILURE

        status = "成功"
        exit_code = EXIT_SUCCESS

        try:
            self.log("--- 任务开始 ---", LogLevel.INFO)
            self.prewarm_ocr()
            self._perform_login()

            # 1. 初始检查
            current_server_list = self._get_servers()
            servers_to_renew = [s for s in current_server_list if s["renewable"]]

            if not current_server_list:
                self.log("账号下无服务器。", LogLevel.WARNING)
                return EXIT_SUCCESS

            # 2. 分支处理
            if not servers_to_renew:
                self.log("所有服务器均无需续期，跳过执行。", LogLevel.SUCCESS)
                exit_code = EXIT_SKIPPED
            else:
                # 执行续期
                if not self._process_server_renewals(servers_to_renew):
                    status = "部分失败"
                    exit_code = EXIT_FAILURE
                
                # 强制刷新状态（含等待）
                current_server_list = self._fetch_server_list_with_retry()

            # 3. 统一收尾
            self._finalize_report_and_schedule(current_server_list)
            self.log("--- 任务完成 ---", LogLevel.CELEBRATION)

        except (LoginError, RenewalError, PinRetrievalError, CaptchaError) as e:
            status = "失败"
            exit_code = EXIT_FAILURE
            self.log(f"运行时致命错误: {e}", LogLevel.ERROR)
        finally:
            self._cleanup()
            self.send_status_email(status)

        return exit_code

def main() -> None:
    bot = RenewalBot()
    exit_code = bot.run()
    exit(exit_code)

if __name__ == "__main__":
    main()
