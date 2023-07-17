class GeneralConfig:
    def __init__(
        self, parallel_mode: bool, ui_mode: bool, debug_mode: bool, secure_hash: bool
    ):

        # validate config
        self.parallel_mode = parallel_mode
        self.ui_mode = ui_mode
        self.debug_mode = debug_mode
        self.secure_hash = secure_hash

    def __str__(self):
        return (
            f"[general config] parallel Mode: {self.parallel_mode}\n"
            f"[general config] UI Mode: {self.ui_mode}\n"
            f"[general config] Debug Mode: {self.debug_mode}"
        )
