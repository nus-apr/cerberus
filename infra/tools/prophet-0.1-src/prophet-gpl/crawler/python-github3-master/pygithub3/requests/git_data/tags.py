# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.git_data import Tag


class Get(Request):
    uri = 'repos/{user}/{repo}/git/tags/{sha}'
    resource = Tag


class Create(Request):
    uri = 'repos/{user}/{repo}/git/tags'
    resource = Tag
    body_schema = {
        'schema': ('tag', 'message', 'object', 'type', 'tagger'),
        'required': ('type',),
    }
