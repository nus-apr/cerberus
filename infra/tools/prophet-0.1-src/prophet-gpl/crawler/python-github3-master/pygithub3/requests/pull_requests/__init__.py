# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request, ValidationError
from pygithub3.resources.pull_requests import PullRequest, File
from pygithub3.resources.repos import Commit


class List(Request):
    uri = 'repos/{user}/{repo}/pulls'
    resource = PullRequest


class Get(Request):
    uri = 'repos/{user}/{repo}/pulls/{number}'
    resource = PullRequest


class Create(Request):
    uri = 'repos/{user}/{repo}/pulls'
    resource = PullRequest
    body_schema = {
        'schema': ('title', 'body', 'base', 'head', 'issue'),
        'required': ('base', 'head'),
    }

    def clean_body(self):
        if (not ('title' in self.body and 'body' in self.body) and
            not 'issue' in self.body):
            raise ValidationError('pull request creation requires either an '
                                  'issue number or a title and body')
        return self.body


class Update(Request):
    uri = 'repos/{user}/{repo}/pulls/{number}'
    resource = PullRequest
    body_schema = {
        'schema': ('title', 'body', 'state'),
        'required': (),
    }

    def clean_body(self):
        if ('state' in self.body and
            self.body['state'] not in ['open', 'closed']):
            raise ValidationError('If a state is specified, it must be one '
                                  'of "open" or "closed"')
        return self.body


class List_commits(Request):
    uri = 'repos/{user}/{repo}/pulls/{number}/commits'
    resource = Commit


class List_files(Request):
    uri = 'repos/{user}/{repo}/pulls/{number}/files'
    resource = File


class Is_merged(Request):
    uri = 'repos/{user}/{repo}/pulls/{number}/merge'


class Merge(Request):
    uri = 'repos/{user}/{repo}/pulls/{number}/merge'
    body_schema = {
        'schema': ('commit_message',),
        'required': (),
    }
