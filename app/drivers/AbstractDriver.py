import abc
from typing import Any
from typing import NoReturn

from app.core import emitter
from app.core import values


class AbstractDriver:
    def _emit_normal_raw(self, abstraction: str, concrete: str, message: Any) -> None:
        emitter.normal(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def _emit_warning_raw(self, abstraction: str, concrete: str, message: Any) -> None:
        emitter.warning(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def _emit_error_raw(self, abstraction: str, concrete: str, message: Any) -> None:
        emitter.error(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def _emit_highlight_raw(
        self, abstraction: str, concrete: str, message: Any
    ) -> None:
        emitter.highlight(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def _emit_success_raw(self, abstraction: str, concrete: str, message: Any) -> None:
        emitter.success(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def _emit_debug_raw(self, abstraction: str, concrete: str, message: Any) -> None:
        emitter.debug(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def error_exit(self, message: Any) -> NoReturn:
        raise Exception(message)
