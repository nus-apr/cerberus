class ToolConfig:
    def __init__(
        self,
        name: str,
        params: str,
        tag: str = "",
        image: str = "",
        hash_digest: str = "",
    ):
        self.tag = tag
        self.name = name
        self.params = params
        self.image = image
        self.hash_digest = hash_digest
