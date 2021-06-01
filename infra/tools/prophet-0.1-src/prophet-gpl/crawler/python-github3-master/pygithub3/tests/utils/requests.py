#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from .base import Request
from pygithub3.exceptions import ValidationError


class RequestWithArgs(Request):

    uri = 'URI/{arg1}/{arg2}'


class RequestCleanedUri(Request):

    uri = 'URI/{arg1}/{arg2}'

    def clean_uri(self):
        if not self.arg1:
            return 'URI'


class RequestBodyInvalidSchema(Request):
    """ It's invalid because body_schema[required] isn't a subset of
    body_schema[schema] """
    uri = 'URI'
    body_schema = {
        'schema': ('arg1', 'arg2'),
        'required': ('arg3', )
    }


class RequestCleanedBody(Request):

    uri = 'URI'

    def clean_body(self):
        raise ValidationError('test')
