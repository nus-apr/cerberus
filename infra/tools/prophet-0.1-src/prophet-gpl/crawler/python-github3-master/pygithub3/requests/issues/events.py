# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.issues import Event


class List_by_issue(Request):

    uri = 'repos/{user}/{repo}/issues/{number}/events'
    resource = Event


class List_by_repo(Request):

    uri = 'repos/{user}/{repo}/issues/events'
    resource = Event


class Get(Request):

    uri = 'repos/{user}/{repo}/issues/events/{id}'
    resource = Event
