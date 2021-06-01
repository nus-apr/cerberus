# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request, ValidationError
from pygithub3.resources.issues import Milestone


class List(Request):
    uri = 'repos/{user}/{repo}/milestones'
    resource = Milestone


class Get(Request):
    uri = 'repos/{user}/{repo}/milestones/{number}'
    resource = Milestone


class Create(Request):
    uri = 'repos/{user}/{repo}/milestones'
    resource = Milestone
    body_schema = {
        'schema': ('title', 'state', 'description', 'due_on'),
        'required': ('title',)
    }

    def clean_body(self):  # Test if API normalize it
        state = self.body.get('state', '')
        if state and state.lower() not in ('open', 'closed'):
            raise ValidationError("'state' must be 'open' or 'closed'")
        return self.body


class Update(Create):

    uri = 'repos/{user}/{repo}/milestones/{number}'


class Delete(Request):
    uri = 'repos/{user}/{repo}/milestones/{number}'
    resource = Milestone
