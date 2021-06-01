# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.events import Org


class List(Request):

    uri = 'orgs/{org}/events'
    resource = Org
