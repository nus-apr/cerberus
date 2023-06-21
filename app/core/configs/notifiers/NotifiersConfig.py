from app.core.configs.notifiers.EmailConfig import EmailConfig
from app.core.configs.notifiers.SlackConfig import SlackConfig


class NotifiersConfig:

    def __init__(self, email_config: EmailConfig, slack_config: SlackConfig):
        self.email_config = email_config
        self.slack_config = slack_config

    def get_email_config(self) -> EmailConfig:
        return self.email_config

    def get_slack_config(self) -> SlackConfig:
        return self.slack_config
