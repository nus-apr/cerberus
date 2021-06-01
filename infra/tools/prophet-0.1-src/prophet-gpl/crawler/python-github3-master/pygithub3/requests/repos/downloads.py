#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Request

from pygithub3.resources.repos import Download


class List(Request):

    uri = '/repos/{user}/{repo}/downloads'
    resource = Download


class Get(Request):

    uri = '/repos/{user}/{repo}/downloads/{id}'
    resource = Download


class Create(Request):

    uri = '/repos/{user}/{repo}/downloads'
    resource = Download
    body_schema = {
        'schema': ('name', 'size', 'description', 'content_type'),
        'required': ('name', 'size')
    }


class Delete(Request):

    uri = '/repos/{user}/{repo}/downloads/{id}'
    resource = Download
