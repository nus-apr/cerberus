# -*- encoding: utf-8 -*-

from pygithub3.resources.orgs import Member, Team
from pygithub3.resources.repos import Repo
from . import Request


class List(Request):
    uri = 'orgs/{org}/teams'
    resource = Team


class Get(Request):
    uri = 'teams/{id}'
    resource = Team


class Create(Request):
    uri = 'orgs/{org}/teams'
    resource = Team
    body_schema = {
        'schema': ('name', 'repo_names', 'permission',),
        'required': ('name',),
    }

    # TODO: Check if this request fails with invalid permission
    #def clean_body(self):


class Update(Request):
    uri = 'teams/{id}'
    resource = Team
    body_schema = {
        'schema': ('name', 'permission',),
        'required': ('name',),
    }


class Delete(Request):
    uri = 'teams/{id}'


class List_members(Request):
    uri = 'teams/{id}/members'
    resource = Member


class Is_member(Request):
    uri = 'teams/{id}/members/{user}'


class Add_member(Request):
    uri = 'teams/{id}/members/{user}'


class Remove_member(Request):
    uri = 'teams/{id}/members/{user}'


class List_repos(Request):
    uri = 'teams/{id}/repos'
    resource = Repo


class Contains_repo(Request):
    uri = 'teams/{id}/repos/{user}/{repo}'


class Add_repo(Request):
    uri = 'teams/{id}/repos/{user}/{repo}'


class Remove_repo(Request):
    uri = 'teams/{id}/repos/{user}/{repo}'
