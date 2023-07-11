from typing import Optional

from app.core.configs.notifiers.DiscordConfig import DiscordConfig
from app.core.configs.notifiers.EmailConfig import EmailConfig
from app.core.configs.notifiers.SlackConfig import SlackConfig


class NotifiersConfig:
    def __init__(
        self,
        email_config: Optional[EmailConfig],
        slack_config: Optional[SlackConfig],
        discord_config: Optional[DiscordConfig],
    ):
        self.email_config = email_config
        self.slack_config = slack_config
        self.discord_config = discord_config
