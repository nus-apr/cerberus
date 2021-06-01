# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service
from .blobs import Blobs
from .commits import Commits
from .references import References
from .tags import Tags
from .trees import Trees


class GitData(Service):
    """Consume `Git Data API <http://developer.github.com/v3/git/>`_"""

    def __init__(self, **config):
        self.blobs = Blobs(**config)
        self.commits = Commits(**config)
        self.references = References(**config)
        self.tags = Tags(**config)
        self.trees = Trees(**config)
        super(GitData, self).__init__(**config)
