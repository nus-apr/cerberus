import abc

from app.core import abstractions
from app.core import emitter
from app.core import utilities
from app.core import values


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

    def get_config_value(self, config_name):
        config_val = getattr(values, config_name)  # Same as someClass = foo.Class3
        return config_val

    def error_exit(self, message):
        raise Exception(message)
