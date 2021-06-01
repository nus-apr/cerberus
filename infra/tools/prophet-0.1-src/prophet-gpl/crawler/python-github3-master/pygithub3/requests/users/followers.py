#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.users import User


class List(Request):

    resource = User
    uri = 'users/{user}/followers'

    def clean_uri(self):
        if not self.user:
            return 'user/followers'


class Listfollowing(Request):

    resource = User
    uri = 'users/{user}/following'

    def clean_uri(self):
        if not self.user:
            return 'user/following'


class Isfollowing(Request):

    uri = 'user/following/{user}'


class Follow(Request):

    uri = 'user/following/{user}'


class Unfollow(Request):

    uri = 'user/following/{user}'
