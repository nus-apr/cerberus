# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.orgs import Team
from pygithub3.resources.repos import Repo, Tag, Branch
from pygithub3.resources.users import User


class List(Request):

    uri = 'users/{user}/repos'
    resource = Repo

    def clean_uri(self):
        if not self.user:
            return 'user/repos'


class List_by_org(Request):

    uri = 'orgs/{org}/repos'
    resource = Repo


class Create(Request):

    uri = 'orgs/{org}/repos'
    resource = Repo
    body_schema = {
        'schema': ('name', 'description', 'homepage', 'private', 'has_issues',
                   'has_wiki', 'has_downloads', 'team_id'),
        'required': ('name', )
    }

    def clean_uri(self):
        if not self.org:
            return 'user/repos'


class Get(Request):

    uri = 'repos/{user}/{repo}'
    resource = Repo


class Delete(Request):

    uri = 'repos/{user}/{repo}'
    resource = Repo


class Update(Request):

    uri = 'repos/{user}/{repo}'
    resource = Repo
    body_schema = {
        'schema': ('name', 'description', 'homepage', 'private', 'has_issues',
                   'has_wiki', 'has_downloads', 'team_id'),
        'required': ('name', )
    }


class List_contributors(Request):

    uri = 'repos/{user}/{repo}/contributors'
    resource = User


class List_languages(Request):

    uri = 'repos/{user}/{repo}/languages'


class List_teams(Request):

    uri = 'repos/{user}/{repo}/teams'
    resource = Team


class List_tags(Request):

    uri = 'repos/{user}/{repo}/tags'
    resource = Tag


class List_branches(Request):

    uri = 'repos/{user}/{repo}/branches'
    resource = Branch
