#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Request

from pygithub3.resources.users import Key


class List(Request):

    uri = '/repos/{user}/{repo}/keys'
    resource = Key


class Get(Request):

    uri = '/repos/{user}/{repo}/keys/{id}'
    resource = Key


class Create(Request):

    uri = 'repos/{user}/{repo}/keys'
    resource = Key
    body_schema = {
        'schema': ('title', 'key'),
        'required': ('title', 'key')
    }


class Update(Request):

    uri = 'repos/{user}/{repo}/keys/{id}'
    resource = Key
    body_schema = {
        'schema': ('title', 'key'),
        'required': (),
    }


class Delete(Request):

    uri = 'repos/{user}/{repo}/keys/{id}'
    resource = Key
