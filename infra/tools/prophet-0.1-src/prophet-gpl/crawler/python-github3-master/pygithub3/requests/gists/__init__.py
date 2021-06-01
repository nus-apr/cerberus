# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.gists import Gist


class List(Request):

    uri = 'users/{user}/gists'
    resource = Gist

    def clean_uri(self):
        if not self.user:
            return 'gists'


class Public(Request):

    uri = 'gists/public'
    resource = Gist


class Starred(Request):

    uri = 'gists/starred'
    resource = Gist


class Get(Request):

    uri = 'gists/{id}'
    resource = Gist


class Create(Request):

    uri = 'gists'
    resource = Gist
    body_schema = {
        'schema': ('description', 'public', 'files'),
        'required': ('public', 'files')
    }


class Update(Request):

    uri = 'gists/{id}'
    resource = Gist
    body_schema = {
        'schema': ('description', 'public', 'files'),
        'required': (),
    }


class Star(Request):

    uri = 'gists/{id}/star'


class Unstar(Request):

    uri = 'gists/{id}/star'


class Is_starred(Request):

    uri = 'gists/{id}/star'


class Fork(Request):

    uri = 'gists/{id}/fork'
    resource = Gist


class Delete(Request):

    uri = 'gists/{id}'
