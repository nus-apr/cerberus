from queue import Queue
from typing import Union

from app.core import emitter
import time
from watchdog.events import FileSystemEvent
from watchdog.events import FileCreatedEvent
from watchdog.events import FileSystemEventHandler


class FileCreationHandler(FileSystemEventHandler):
    def __init__(self, q: Queue[Union[str, FileSystemEvent]]) -> None:
        # print("Initializing")
        self.q = q
        self.last_check = time.time()

    def on_created(self, event: FileSystemEvent) -> None:
        # print("Created!")

        # Ignore common metadata files
        if (
            event.src_path.endswith(".metadata")
            or event.src_path.endswith(".tmp")
            or event.src_path.endswith(".metadata.tmp")
            or event.src_path.endswith("lafl_lock")
            or event.src_path.endswith(".swp")
            or event.src_path.endswith(".swpx")
            or event.src_path.endswith(".swx")
            or "timeout" in event.src_path
        ):
            return

        self.q.put(event)

    # Libfuzzer does moves to crashes, unlike AFL which creates a new file
    def on_moved(self, event: FileSystemEvent) -> None:
        if not ("crashes" in event.src_path):
            return

        if event.src_path.endswith(".tmp") and "metadata" not in event.src_path:
            self.q.put(FileCreatedEvent(event.dest_path))
