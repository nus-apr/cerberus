
class ToolConfig:

    def __init__(self, name: str, params: dict):

        self.name = name
        self.params = params

    def get_name(self) -> str:
        return self.name

    def get_params(self) -> dict:
        return self.params
