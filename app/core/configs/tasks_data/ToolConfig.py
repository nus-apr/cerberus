class ToolConfig:
    def __init__(
        self,
        name: str,
        params: str,
        tag: str = "",
        image: str = "",
        hash_digest: str = "",
        ignore: bool = False,
        local: bool = False,
        rebuild: bool = False,
    ):
        self.tag = tag
        self.name = name
        self.params = params
        self.image = image
        self.hash_digest = hash_digest
        self.ignore = ignore
        self.local = local
        self.rebuild = rebuild
