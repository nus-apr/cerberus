#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from datetime import datetime

import requests
from mock import patch

from pygithub3.tests.utils.core import TestCase
from pygithub3.services.base import Service, MimeTypeMixin
from pygithub3.core.result import base
from pygithub3.tests.utils.base import DummyRequest, mock_response
from pygithub3.tests.utils.services import _, DummyService


@patch.object(requests.sessions.Session, 'request')
class TestServiceCalls(TestCase):

    def setUp(self):
        self.s = Service()
        self.r = DummyRequest()
        self.args = dict(arg1='arg1', arg2='arg2')

    def test_BOOL(self, request_method):
        self.s._bool(self.r, **self.args)
        request_method.assert_called_with('head', _('dummyrequest'),
                                          params=self.args)

    def test_PUT(self, request_method):
        self.s._put(self.r, **self.args)
        data = 'PLACEHOLDER'  # See _put
        request_method.assert_called_with('put', _('dummyrequest'),
                                          data=data, params=self.args)

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.s._delete(self.r, **self.args)
        request_method.assert_called_with('delete', _('dummyrequest'),
                                          data=None, params=self.args)

    def test_POST(self, request_method):
        request_method.return_value = mock_response('post')
        self.s._post(self.r, **self.args)
        request_method.assert_called_with('post', _('dummyrequest'),
                                          data=None, params=self.args)

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.s._get(self.r, **self.args)
        request_method.assert_called_with('get', _('dummyrequest'),
                                          params=self.args)

    def test_GET_result(self, request_method):
        result = self.s._get_result(self.r, **self.args)
        self.assertFalse(request_method.called)
        self.assertIsInstance(result, base.Result)


@patch.object(requests.sessions.Session, 'request')
class TestMimeType(TestCase):

    def setUp(self):
        self.ms = DummyService()

    def test_WITHOUT_mimetype(self, request_method):
        request_method.return_value = mock_response()
        self.ms.dummy_request()
        request_method.assert_called_with('get', _('dummyrequest'), params={})

    def test_WITH_mimetype(self, request_method):
        request_method.return_value = mock_response()
        self.ms.set_html()
        self.ms.dummy_request()
        request_method.assert_called_with('get', _('dummyrequest'),
            headers={'Accept': 'application/vnd.github.%s.html+json' %
                                MimeTypeMixin.VERSION},
            params={})
