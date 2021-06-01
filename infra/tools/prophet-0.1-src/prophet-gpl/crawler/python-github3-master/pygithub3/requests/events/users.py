# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.events import User, Org


class List_received(Request):

    uri = 'users/{user}/received_events'
    resource = User


class List_received_public(Request):

    uri = 'users/{user}/received_events/public'
    resource = User


class List_performed(Request):

    uri = 'users/{user}/events'
    resource = User


class List_performed_public(Request):

    uri = 'users/{user}/events/public'
    resource = User


class List_org_events(Request):

    uri = 'users/{user}/events/orgs/{org}'
    resource = Org
