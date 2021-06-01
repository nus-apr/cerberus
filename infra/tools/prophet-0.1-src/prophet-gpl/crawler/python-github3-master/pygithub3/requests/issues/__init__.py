#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.issues import Issue


class List(Request):

    uri = 'issues'
    resource = Issue


class List_by_repo(Request):

    uri = 'repos/{user}/{repo}/issues'
    resource = Issue


class Get(Request):

    uri = 'repos/{user}/{repo}/issues/{number}'
    resource = Issue


class Create(Request):

    uri = 'repos/{user}/{repo}/issues'
    resource = Issue
    body_schema = {
        'schema': ('title', 'body', 'assignee', 'milestone', 'labels'),
        'required': ('title', )
    }


class Update(Request):

    uri = 'repos/{user}/{repo}/issues/{number}'
    resource = Issue
    body_schema = {
        'schema': ('title', 'body', 'assignee', 'state', 'milestone',
                   'lables'),
        'required': ()
    }
