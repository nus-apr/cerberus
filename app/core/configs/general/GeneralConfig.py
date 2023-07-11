class GeneralConfig:
    def __init__(self, parallel_mode: bool, ui_mode: bool):

        # validate config
        self.parallel_mode = parallel_mode
        self.ui_mode = ui_mode

    def is_parallel_mode(self) -> bool:
        return self.parallel_mode

    def is_ui_mode(self) -> bool:
        return self.ui_mode

    def __str__(self):
        return (
            f"[general config] parallel Mode: {self.parallel_mode}\n"
            f"[general config] UI Mode: {self.ui_mode}"
        )
