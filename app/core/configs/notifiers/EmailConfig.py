from typing import List

from app.core.configs.notifiers.AbstractNotifierConfig import AbstractNotifierConfig


class EmailConfig(AbstractNotifierConfig):
    def __init__(
        self,
        enable: bool,
        username: str,
        password: str,
        host: str,
        port: int,
        ssl_from_start: bool,
        recipients: List[str],
    ):

        super().__init__(enable)
        self.username = username
        self.password = password
        self.host = host
        self.port = port
        self.recipients = recipients
        self.ssl_from_start = ssl_from_start
