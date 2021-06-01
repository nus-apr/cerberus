# -*- encoding: utf-8 -*-

from pygithub3.requests.base import Request, ValidationError
from pygithub3.resources.users import User


class Get(Request):

    resource = User
    uri = 'users/{user}'

    def clean_uri(self):
        if not self.user:
            return 'user'


class Update(Request):

    resource = User
    uri = 'user'
    body_schema = {
        'schema': ('name', 'email', 'blog', 'company', 'location', 'hireable',
                   'bio'),
        'required': (),
    }

    def clean_body(self):
        if not self.body:
            raise ValidationError("'%s' request needs data. You can use "
                                  "'%s' keys" % (self.__class__.__name__,
                                  self.body_schema))
        return self.body
