#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from .base import Resource
from .repos import Author, Commit


class Blob(Resource):
    def __str__(self):
        return "<Blob (%s)>" % getattr(self, 'content', '')


class Reference(Resource):
    def __str__(self):
        return '<Reference (%s)>' % getattr(self, 'ref', '')


class Tag(Resource):
    _maps = {'object': Commit,
             'tagger': Author}  # committer? tagger?

    def __str__(self):
        return '<Tag (%s)>' % getattr(self, 'tag', '')


class Tree(Resource):
    def __str__(self):
        return '<Tree (%s)>' % getattr(self, 'sha', '')
