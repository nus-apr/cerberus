# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.events import Network


class List(Request):

    uri = 'networks/{user}/{repo}/events'
    resource = Network
