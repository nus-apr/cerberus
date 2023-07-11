from app.core.configs.notifiers.AbstractNotifierConfig import AbstractNotifierConfig


class DiscordConfig(AbstractNotifierConfig):
    def __init__(self, enable: bool, hook_url: str):
        super().__init__(enable)
        self.hook_url = hook_url
