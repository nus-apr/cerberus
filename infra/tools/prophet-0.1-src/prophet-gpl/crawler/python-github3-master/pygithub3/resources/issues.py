#!/usr/bin/env python
# -*- encoding: utf-8 -*-

import re

from .base import Resource
from .users import User
from .pull_requests import PullRequest


class Label(Resource):

    @staticmethod
    def is_valid_color(color):
        valid_color = re.compile(r'[0-9abcdefABCDEF]{6}')
        match = valid_color.match(color)
        if match is None:
            return False
        return match.start() == 0 and match.end() == len(color)

    def __str__(self):
        return '<Label (%s)>' % getattr(self, 'name', '')


class Milestone(Resource):

    _dates = ('created_at', 'due_on')
    _maps = {'creator': User}

    def __str__(self):
        return '<Milestone (%s)>' % getattr(self, 'title', '')


class Issue(Resource):

    _dates = ('created_at', 'updated_at', 'closed_at')
    _maps = {
        'assignee': User,
        'user': User,
        'milestone': Milestone,
        'pull_request': PullRequest
    }

    _collection_maps = {'labels': Label}

    def __str__(self):
        return '<Issue (%s)>' % getattr(self, 'number', '')


class Comment(Resource):

    _dates = ('created_at', 'updated_at')
    _maps = {'user': User}

    def __str__(self):
        return '<Comment (%s)>' % (getattr(self, 'user', ''))


class Event(Resource):

    _dates = ('created_at', )
    _maps = {'actor': User, 'issue': Issue}

    def __str__(self):
        return '<Event (%s)>' % (getattr(self, 'commit_id', ''))
