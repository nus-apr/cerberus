#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Request

from pygithub3.resources.repos import Repo


class List(Request):

    uri = 'repos/{user}/{repo}/forks'
    resource = Repo


class Create(Request):

    uri = '/repos/{user}/{repo}/forks'
    resource = Repo
