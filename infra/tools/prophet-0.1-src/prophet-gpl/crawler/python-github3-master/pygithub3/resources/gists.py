# -*- encoding: utf-8 -*-

from .base import Resource
from .users import User


class File(Resource):

    def __str__(self):
        return '<GistFile (%s)>' % getattr(self, 'filename', '')


class Fork(Resource):

    _dates = ('created_at', )
    _maps = {'user': User}

    def __str__(self):
        return '<GistFork>'


class History(Resource):

    _dates = ('committed_at', )
    _maps = {'user': User}

    def __str__(self):
        return '<GistHistory (%s)>' % getattr(self, 'version', '')


class Gist(Resource):

    _dates = ('created_at', )
    _maps = {'user': User}
    _collection_maps = {'files': File, 'forks': Fork, 'history': History}

    def __str__(self):
        return '<Gist (%s)>' % getattr(self, 'description', '')


class Comment(Resource):

    _dates = ('created_at', )
    _maps = {'user': User}

    def __str__(self):
        return '<GistComment (%s)>' % getattr(self, 'user', '')
