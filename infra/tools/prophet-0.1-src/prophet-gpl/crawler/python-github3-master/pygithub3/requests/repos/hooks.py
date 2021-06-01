#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.repos import Hook


class List(Request):

    uri = 'repos/{user}/{repo}/hooks'
    resource = Hook


class Get(Request):

    uri = 'repos/{user}/{repo}/hooks/{id}'
    resource = Hook


class Create(Request):

    uri = 'repos/{user}/{repo}/hooks'
    resource = Hook
    body_schema = {
        'schema': ('name', 'config', 'events', 'active'),
        'required': ('name', 'config'),
    }


class Update(Request):

    uri = 'repos/{user}/{repo}/hooks/{id}'
    resource = Hook
    body_schema = {
        'schema': ('name', 'config', 'events', 'add_events', 'remove_events',
                    'active'),
        'required': (),
    }


class Test(Request):

    uri = 'repos/{user}/{repo}/hooks/{id}/test'


class Delete(Request):

    uri = 'repos/{user}/{repo}/hooks/{id}'
