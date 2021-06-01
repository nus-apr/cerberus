# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.git_data import Reference


class Get(Request):
    uri = 'repos/{user}/{repo}/git/refs/{ref}'
    resource = Reference


class List(Request):
    uri = 'repos/{user}/{repo}/git/refs/{namespace}'
    resource = Reference


class Create(Request):
    uri = 'repos/{user}/{repo}/git/refs'
    resource = Reference
    body_schema = {
        'schema': ('ref', 'sha'),
        'required': ('ref', 'sha'),
    }


class Update(Request):
    uri = 'repos/{user}/{repo}/git/refs/{ref}'
    resource = Reference
    body_schema = {
        'schema': ('sha', 'force'),
        'required': ('sha',),
    }


class Delete(Request):
    uri = 'repos/{user}/{repo}/git/refs/{ref}'
