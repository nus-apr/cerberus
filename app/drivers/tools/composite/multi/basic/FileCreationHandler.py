from queue import Queue
from typing import Union

from watchdog.events import FileSystemEvent
from watchdog.events import FileSystemEventHandler


class FileCreationHandler(FileSystemEventHandler):
    def __init__(self, q: Queue[Union[str, FileSystemEvent]]) -> None:
        # print("Initializing")
        self.q = q

    def on_created(self, event: FileSystemEvent) -> None:
        # print("Created!")
        self.q.put(event)
