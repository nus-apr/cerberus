#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.users import User
from pygithub3.resources.repos import Repo


class List(Request):

    uri = 'repos/{user}/{repo}/watchers'
    resource = User


class List_repos(Request):

    uri = 'users/{user}/watched'
    resource = Repo

    def clean_uri(self):
        if not self.user:
            return 'user/watched'


class Is_watching(Request):

    uri = 'user/watched/{user}/{repo}'


class Watch(Request):

    uri = 'user/watched/{user}/{repo}'


class Unwatch(Request):

    uri = 'user/watched/{user}/{repo}'
