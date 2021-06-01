# -*- encoding: utf-8 -*-

from pygithub3.resources.base import Resource
from pygithub3.resources import users, repos, orgs


class Event(Resource):

    _dates = ('created_at', )
    _maps = {'actor': users.User, 'repo': repos.Repo, 'org': orgs.Org}

    def __str__(self):
        return '<(%s)>' % getattr(self, 'type', '')


class Repo(Resource):

    _dates = ('created_at', )
    _maps = {'actor': users.User, 'repo': repos.Repo, 'org': orgs.Org}

    def __str__(self):
        return '<(%s)>' % getattr(self, 'type', '')


class Network(Resource):

    _dates = ('created_at', )
    _maps = {'actor': users.User, 'repo': repos.Repo, 'org': orgs.Org}

    def __str__(self):
        return '<(%s)>' % getattr(self, 'type', '')


class Org(Resource):

    _dates = ('created_at', )
    _maps = {'actor': users.User, 'repo': repos.Repo, 'org': orgs.Org}

    def __str__(self):
        return '<(%s)>' % getattr(self, 'type', '')


class User(Resource):

    _dates = ('created_at', )
    _maps = {'actor': users.User, 'repo': repos.Repo, 'org': orgs.Org}

    def __str__(self):
        return '<(%s)>' % getattr(self, 'type', '')
