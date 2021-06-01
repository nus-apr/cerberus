# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request
from pygithub3.resources.orgs import Org


class List(Request):
    uri = 'users/{user}/orgs'
    resource = Org

    def clean_uri(self):
        if not self.user:
            return 'user/orgs'


class Get(Request):
    uri = 'orgs/{org}'
    resource = Org


class Update(Request):
    uri = 'orgs/{org}'
    resource = Org
    body_schema = {
        'schema': ('billing_email', 'company', 'email', 'location', 'name'),
        'required': (),
    }
