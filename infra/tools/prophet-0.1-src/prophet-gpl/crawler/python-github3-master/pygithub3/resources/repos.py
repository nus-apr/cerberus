#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.core.compat import OrderedDict

from .base import Resource
from .users import User
from .orgs import Org


class Repo(Resource):

    _dates = ('created_at', 'updated_at', 'pushed_at')
    _maps = {'owner': User, 'organization': Org, 'parent': 'self',
             'source': 'self'}

    def __str__(self):
        return '<Repo (%s)>' % getattr(self, 'name', '')


class Author(Resource):

    _dates = ('date')

    def __str__(self):
        return '<Author (%s)>' % getattr(self, 'name', '')


class Committer(Resource):

    _dates = ('date')

    def __str__(self):
        return '<Committer (%s)>' % getattr(self, 'name', '')


class Commit(Resource):

    _maps = {'author': Author, 'committer': Committer}
    #_maps.update({'tree': GitCommit})

    def __str__(self):
        return '<Commit (%s)>' % getattr(self, 'author', '')


class Stats(Resource):
    pass


class File(Resource):

    def __str__(self):
        return '<File (%s)>' % getattr(self, 'filename', '')


class GitCommit(Resource):

    _maps = {'author': User, 'committer': User, 'commit': Commit,
             'stats': Stats}
    _collection_maps = {'parents': 'self', 'files': File}

    def __str__(self):
        return '<GitCommit (%s)>' % getattr(self, 'sha', '')


class Comment(Resource):

    _dates = ('created_at', 'updated_at')
    _maps = {'user': User}

    def __str__(self):
        return '<Comment (%s)>' % getattr(self, 'user', '')


class Diff(Resource):

    _maps = {'base_commit': Commit}
    _collection_maps = {'commits': Commit, 'files': File}

    def __str__(self):
        return '<Diff (%s)>' % getattr(self, 'status', '')


class Tag(Resource):

    _maps = {'commit': GitCommit}

    def __str__(self):
        return '<Tag (%s)>' % getattr(self, 'name', '')


class Branch(Resource):

    _maps = {'commit': GitCommit}

    def __str__(self):
        return '<Branch (%s)>' % getattr(self, 'name', '')


class Download(Resource):

    def __str__(self):
        return '<Download (%s)>' % getattr(self, 'name', '')

    def ball_to_upload(self):
        return OrderedDict({
            'key': self.path, 'acl': self.acl, 'success_action_status': '201',
            'Filename': self.name, 'AWSAccessKeyId': self.accesskeyid,
            'Policy': self.policy, 'Signature': self.signature,
            'Content-Type': self.mime_type})


class Hook(Resource):

    _dates = ('created_at', 'pushed_at')

    def __str__(self):
        return '<Hook (%s)>' % getattr(self, 'name', '')
