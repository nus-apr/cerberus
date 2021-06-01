# -*- encoding: utf-8 -*-

from .base import Resource


class PullRequest(Resource):
    _dates = ('created_at', 'updated_at', 'closed_at', 'merged_at')

    def __str__(self):
        return '<PullRequest (%s)>' % getattr(self, 'title', '')


class File(Resource):
    def __str__(self):
        return '<File (%s)>' % getattr(self, 'filename', '')


class Comment(Resource):
    _dates = ('created_at', 'updated_at')

    def __str__(self):
        return '<Comment (#%s)>' % getattr(self, 'id', '')
