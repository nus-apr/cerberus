#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.users import User


class List(Request):

    uri = 'repos/{user}/{repo}/collaborators'
    resource = User


class Is_collaborator(Request):

    uri = 'repos/{user}/{repo}/collaborators/{collaborator}'


class Add(Request):

    uri = 'repos/{user}/{repo}/collaborators/{collaborator}'


class Delete(Request):

    uri = 'repos/{user}/{repo}/collaborators/{collaborator}'
