from queue import Queue

from watchdog.events import FileSystemEvent
from watchdog.events import FileSystemEventHandler


class FileCreationHandler(FileSystemEventHandler):
    def __init__(self, q: Queue):
        # print("Initializing")
        self.q = q

    def on_created(self, event: FileSystemEvent):
        # print("Created!")
        self.q.put(event)
