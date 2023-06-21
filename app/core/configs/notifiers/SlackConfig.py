from app.core.configs.notifiers.AbstractNotifierConfig import AbstractNotifierConfig


class SlackConfig(AbstractNotifierConfig):

    def __init__(self, enable: bool, hook_url: str, oauth_token: str, channel: str):
        super().__init__(enable)
        self.hook_url = hook_url
        self.oauth_token = oauth_token
        self.channel = channel

    def get_hook_url(self) -> str:
        return self.hook_url

    def get_oauth_token(self) -> str:
        return self.oauth_token

    def get_channel(self) -> str:
        return self.channel
