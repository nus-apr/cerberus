# -*- encoding: utf-8 -*-

import re

from pygithub3.core import json
from pygithub3.core.compat import import_module
from pygithub3.exceptions import (RequestDoesNotExist, UriInvalid,
                                  ValidationError, InvalidBodySchema)
from pygithub3.resources.base import Raw

ABS_IMPORT_PREFIX = 'pygithub3.requests'


class Body(object):
    """ Input's request handler """

    def __init__(self, content, schema, required):
        self.content = content
        self.schema = schema
        self.required = required

    def dumps(self):
        if not self.schema:
            return self.content or None
        return json.dumps(self.parse())

    def parse(self):
        """ Parse body with schema-required rules """
        if not hasattr(self.content, 'items'):
            raise ValidationError("It needs a content dictionary (%s)" % (
                self.content, ))
        parsed = dict([(key, self.content[key]) for key in self.schema
                      if key in self.content])
        for attr_required in self.required:
            if attr_required not in parsed:
                raise ValidationError("'%s' attribute is required" %
                                      attr_required)
            if parsed[attr_required] is None:
                raise ValidationError("'%s' attribute can't be empty" %
                                      attr_required)
        return parsed


class Request(object):

    uri = ''
    resource = Raw
    body_schema = {}

    def __init__(self, **kwargs):
        self.body = kwargs.pop('body', {})
        self.args = kwargs
        self.clean()

    def __getattr__(self, name):
        return self.args.get(name)

    def __str__(self):
        return self.populate_uri()

    def populate_uri(self):
        try:
            populated_uri = self.uri.format(**self.args)
        except KeyError:
            raise ValidationError(
                "'%s' request wasn't be able to populate the uri '%s' with "
                "'%s' args" % (self.__class__.__name__, self.uri, self.args))
        return str(populated_uri).strip('/')

    def clean(self):
        self.uri = self.clean_uri() or self.uri
        self.body = Body(self.clean_body(), **self._clean_valid_body())

    def clean_body(self):
        return self.body

    def clean_uri(self):
        return None

    def _clean_valid_body(self):
        schema = set(self.body_schema.get('schema', ()))
        required = set(self.body_schema.get('required', ()))
        if not required.issubset(schema):
            raise InvalidBodySchema(
                "'%s:valid_body' attribute is invalid. "
                "'%s required' isn't a subset of '%s schema'" % (
                self.__class__.__name__, required, schema))
        return dict(schema=schema, required=required)

    def get_body(self):
        return self.body.dumps()


class Factory(object):
    """ Request builder """

    import_pattern = re.compile(r'^(\w+\.)+\w+$')

    def validate(func):
        """ Decorator to check if request_uri
        has valid format: 'from.path.module.class' """

        def wrapper(self, request_uri, **kwargs):
            if not Factory.import_pattern.match(request_uri):
                raise UriInvalid("'%s' isn't valid form" % request_uri)
            return func(self, request_uri.lower(), **kwargs)
        return wrapper

    @validate
    def __call__(self, request_uri, **kwargs):
        module_chunk, s, request_chunk = request_uri.rpartition('.')
        request_chunk = request_chunk.capitalize()
        try:
            #  TODO: CamelCase and under_score support, now only Class Name
            module = import_module('%s.%s' % (ABS_IMPORT_PREFIX, module_chunk))
            request_class = getattr(module, request_chunk)
            request = request_class(**kwargs)
            assert isinstance(request, Request)
            return request
        except ImportError:
            raise RequestDoesNotExist("'%s' module does not exist"
                                      % module_chunk)
        except AttributeError:
            raise RequestDoesNotExist("'%s' request does not exist in "
                                      "'%s' module" % (request_chunk,
                                      module_chunk))
