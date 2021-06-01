# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.repos import Commit


class Get(Request):
    uri = 'repos/{user}/{repo}/git/commits/{sha}'
    resource = Commit


class Create(Request):
    uri = 'repos/{user}/{repo}/git/commits'
    resource = Commit
    body_schema = {
        'schema': ('message', 'tree', 'parents', 'author', 'committer'),
        'required': ('message', 'tree', 'parents'),
    }
