from typing import List

from app.core.configs.notifiers.AbstractNotifierConfig import AbstractNotifierConfig


class EmailConfig(AbstractNotifierConfig):

    def __init__(self,
                 enable: bool,
                 username: str,
                 password: str,
                 host: str,
                 port: int,
                 ssl_from_start: bool,
                 recipients: List[str]
                 ):

        super().__init__(enable)
        self.username = username
        self.password = password
        self.host = host
        self.port = port
        self.recipients = recipients
        self.ssl_from_start = ssl_from_start

    def get_username(self) -> str:
        return self.username

    def get_password(self) -> str:
        return self.password

    def get_host(self) -> str:
        return self.host

    def get_port(self) -> int:
        return self.port

    def get_recipients(self) -> List[str]:
        return self.recipients

    def is_ssl_from_start(self) -> bool:
        return self.ssl_from_start

