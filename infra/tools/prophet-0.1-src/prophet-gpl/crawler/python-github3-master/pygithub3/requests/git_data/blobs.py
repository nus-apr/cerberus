# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.git_data import Blob


class Get(Request):
    uri = 'repos/{user}/{repo}/git/blobs/{sha}'
    resource = Blob


class Create(Request):
    uri = 'repos/{user}/{repo}/git/blobs'
    resource = Blob
    body_schema = {
        'schema': ('content', 'encoding'),
        'required': ('content', 'encoding'),  # TODO: is enc really required?
    }
