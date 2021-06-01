# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.gists import Comment


class List(Request):

    uri = 'gists/{gist_id}/comments'
    resource = Comment


class Get(Request):

    uri = 'gists/comments/{id}'
    resource = Comment


class Create(Request):

    uri = 'gists/{gist_id}/comments'
    resource = Comment
    body_schema = {
        'schema': ('body', ),
        'required': ('body', )
    }


class Update(Request):

    uri = 'gists/comments/{id}'
    resource = Comment
    body_schema = {
        'schema': ('body', ),
        'required': ('body', )
    }


class Delete(Request):

    uri = 'gists/comments/{id}'
