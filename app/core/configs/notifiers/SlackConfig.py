from app.core.configs.notifiers.AbstractNotifierConfig import AbstractNotifierConfig


class SlackConfig(AbstractNotifierConfig):
    def __init__(self, enable: bool, hook_url: str, oauth_token: str, channel: str):
        super().__init__(enable)
        self.hook_url = hook_url
        self.oauth_token = oauth_token
        self.channel = channel
