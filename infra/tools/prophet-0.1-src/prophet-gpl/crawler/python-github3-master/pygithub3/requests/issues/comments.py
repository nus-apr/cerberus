# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.issues import Comment


class List(Request):

    uri = 'repos/{user}/{repo}/issues/{number}/comments'
    resource = Comment


class Get(Request):

    uri = 'repos/{user}/{repo}/issues/comments/{id}'
    resource = Comment


class Create(Request):

    uri = 'repos/{user}/{repo}/issues/{number}/comments'
    resource = Comment
    body_schema = {
        'schema': ('body', ),
        'required': ('body', )
    }


class Edit(Request):

    uri = 'repos/{user}/{repo}/issues/comments/{id}'
    resource = Comment
    body_schema = {
        'schema': ('body', ),
        'required': ('body', )
    }


class Delete(Request):

    uri = 'repos/{user}/{repo}/issues/comments/{id}'
    resource = Comment
