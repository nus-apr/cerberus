#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.users import Key


class List(Request):

    resource = Key
    uri = 'user/key'


class Get(Request):

    resource = Key
    uri = 'user/keys/{key_id}'


class Add(Request):

    resource = Key
    uri = 'user/keys'
    body_schema = {
        'schema': ('title', 'key'),
        'required': ('title', 'key')
    }


class Update(Request):

    resource = Key
    body_schema = {
        'schema': ('title', 'key'),
        'required': ('title', 'key')
    }
    uri = 'user/keys/{key_id}'


class Delete(Request):

    uri = 'user/keys/{key_id}'
