import smtplib
from email.mime.text import MIMEText
from email.utils import formataddr

from app.core.configs.notifiers.EmailConfig import EmailConfig


class EmailNotifyInt:

    def __init__(self, config: EmailConfig):
        self.config = config
        self.emails = {}

    def send_message(self, text, subject="Cerberus status update"):

        msg = MIMEText(text)

        msg["Subject"] = subject
        msg["From"] = formataddr(("Cerberus", "cerberus-noreply@comp.nus.edu.sg"))
        msg["To"] = self.config.get_recipients()
        # maybe join required

        client = (smtplib.SMTP_SSL if self.config.is_ssl_from_start() else smtplib.SMTP)
        with client(self.config.get_host()) as s:
            s.login(self.config.get_username(),self.config.get_password())
            s.sendmail(self.config.get_username(), self.config.get_recipients(), msg.as_string())
