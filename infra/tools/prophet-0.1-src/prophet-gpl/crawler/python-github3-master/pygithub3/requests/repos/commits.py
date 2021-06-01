#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Request
from pygithub3.resources.repos import GitCommit, Comment, Diff


class List(Request):

    uri = 'repos/{user}/{repo}/commits'
    resource = GitCommit


class Get(Request):

    uri = 'repos/{user}/{repo}/commits/{sha}'
    resource = GitCommit


class List_comments(Request):

    uri = 'repos/{user}/{repo}/comments'
    resource = Comment

    def clean_uri(self):
        if self.sha:
            return 'repos/{user}/{repo}/commits/{sha}/comments'


class Create_comment(Request):

    uri = 'repos/{user}/{repo}/commits/{sha}/comments'
    resource = Comment
    body_schema = {
        'schema': ('body', 'commit_id', 'line', 'path', 'position'),
        'required': ('body', 'commit_id', 'line', 'path', 'position'),
    }


class Get_comment(Request):

    uri = 'repos/{user}/{repo}/comments/{comment_id}'
    resource = Comment


class Update_comment(Request):

    uri = 'repos/{user}/{repo}/comments/{comment_id}'
    resource = Comment
    body_schema = {
        'schema': ('body', ),
        'required': ('body', ),
    }


class Compare(Request):

    uri = 'repos/{user}/{repo}/compare/{base}...{head}'
    resource = Diff


class Delete_comment(Request):

    uri = 'repos/{user}/{repo}/comments/{comment_id}'
