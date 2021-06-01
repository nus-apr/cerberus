# -*- encoding: utf-8 -*-

from mock import Mock, patch

from pygithub3.core import json
from pygithub3.resources.base import Resource
from pygithub3.requests.base import Request


_dummy_json = lambda x, **kwargs: x


def dummy_json(cls):
    return patch.multiple(json, dumps=_dummy_json, loads=_dummy_json)(cls)


def mock_response(status_code='get', content={}):
    CODES = dict(get=200, patch=200, post=201, delete=204)
    response = Mock(name='response')
    response.status_code = CODES.get(str(status_code).lower(), status_code)
    response.content = content
    return response


def mock_response_result(status_code='get'):
    response = mock_response(status_code, content=[{}, {}])
    response.headers = {'link': ''}
    return response


class DummyResource(Resource):

    loads = Mock(side_effect=_dummy_json)


class DummyRequest(Request):
    uri = 'dummyrequest'
    resource = DummyResource
