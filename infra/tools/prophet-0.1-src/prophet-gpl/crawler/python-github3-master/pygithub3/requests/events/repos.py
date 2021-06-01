# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.events import Repo


class List(Request):

    uri = 'repos/{user}/{repo}/events'
    resource = Repo
