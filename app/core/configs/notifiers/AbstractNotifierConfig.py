
class AbstractNotifierConfig:

    def __init__(self, enable: bool):
        self.enable = enable

    def is_enabled(self) -> bool:
        return self.enable
