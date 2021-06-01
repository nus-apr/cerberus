#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.core import json
from pygithub3.exceptions import NotFound, BadRequest, UnprocessableEntity


class GithubError(object):
    """ Handler for API errors """

    def __init__(self, response):
        self.response = response
        self.status_code = response.status_code
        try:
            self.debug = json.loads(response.content)
        except (ValueError, TypeError):
            self.debug = {'message': response.content}

    def error_404(self):
        raise NotFound("404 - %s" % self.debug.get('message'))

    def error_400(self):
        raise BadRequest("400 - %s" % self.debug.get('message'))

    def error_422(self):
        errors = self.debug.get('errors', ())
        errors = ['Resource: {resource}: {field} => {code}'.format(**error)
                 for error in errors]
        raise UnprocessableEntity(
            '422 - %s %s' % (self.debug.get('message'), errors))

    def process(self):
        raise_error = getattr(self, 'error_%s' % self.status_code, False)
        if raise_error:
            raise raise_error()
        self.response.raise_for_status()
