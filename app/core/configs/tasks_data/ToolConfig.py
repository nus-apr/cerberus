class ToolConfig:
    def __init__(self, name: str, params: str, tag: str = "", image: str = ""):
        self.tag = tag
        self.name = name
        self.params = params
        self.image = image
