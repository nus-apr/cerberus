import abc

from app.core import emitter


class AbstractDriver:
    @abc.abstractmethod
    def emit_normal(self, abstraction, concrete, message):
        emitter.normal(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def emit_warning(self, abstraction, concrete, message):
        emitter.warning(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def emit_error(self, abstraction, concrete, message):
        emitter.error(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def emit_highlight(self, abstraction, concrete, message):
        emitter.highlight(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def emit_success(self, abstraction, concrete, message):
        emitter.success(f"\t\t\t[{abstraction}][{concrete}] {message}")

    def emit_debug(self, abstraction, concrete, message):
        emitter.debug(f"\t\t\t[{abstraction}][{concrete}] {message}")
