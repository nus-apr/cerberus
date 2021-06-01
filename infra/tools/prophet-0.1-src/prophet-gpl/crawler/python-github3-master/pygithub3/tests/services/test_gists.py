# -*- encoding: utf-8 -*-

import requests
from mock import patch

from pygithub3.services.gists import Gist, Comments
from pygithub3.tests.utils.base import (dummy_json, mock_response,
    mock_response_result)
from pygithub3.tests.utils.core import TestCase
from pygithub3.tests.utils.services import _


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestGistService(TestCase):

    def setUp(self):
        self.gs = Gist()

    def test_LIST_without_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.gs.list().all()
        self.assertEqual(request_method.call_args[0], ('get', _('gists')))

    def test_LIST_with_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.gs.list('octocat').all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('users/octocat/gists')))

    def test_LIST_public(self, request_method):
        request_method.return_value = mock_response_result()
        self.gs.public().all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('gists/public')))

    def test_LIST_starred(self, request_method):
        request_method.return_value = mock_response_result()
        self.gs.starred().all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('gists/starred')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.gs.get(1)
        self.assertEqual(request_method.call_args[0],
            ('get', _('gists/1')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.gs.create(dict(public=True, files={
            'file1.txt': {'content': 'Some\ncontent'}}))
        self.assertEqual(request_method.call_args[0],
            ('post', _('gists')))

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response('patch')
        self.gs.update(1, {'description': 'edited'})
        self.assertEqual(request_method.call_args[0],
            ('patch', _('gists/1')))

    def test_STAR(self, request_method):
        self.gs.star(1)
        self.assertEqual(request_method.call_args[0],
            ('put', _('gists/1/star')))

    def test_UNSTAR(self, request_method):
        request_method.return_value = mock_response('delete')
        self.gs.unstar(1)
        self.assertEqual(request_method.call_args[0],
            ('delete', _('gists/1/star')))

    def test_IS_STARRED(self, request_method):
        request_method.return_value = mock_response()
        self.gs.is_starred(1)
        self.assertEqual(request_method.call_args[0],
            ('head', _('gists/1/star')))

    def test_FORK(self, request_method):
        request_method.return_value = mock_response('post')
        self.gs.fork(1)
        self.assertEqual(request_method.call_args[0],
            ('post', _('gists/1/fork')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.gs.delete(1)
        self.assertEqual(request_method.call_args[0],
            ('delete', _('gists/1')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestCommentService(TestCase):

    def setUp(self):
        self.cs = Comments()

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.cs.list(1).all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('gists/1/comments')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.cs.get(1)
        self.assertEqual(request_method.call_args[0],
            ('get', _('gists/comments/1')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.cs.create(1, dict(body='comment'))
        self.assertEqual(request_method.call_args[0],
            ('post', _('gists/1/comments')))

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response('patch')
        self.cs.update(1, dict(body='new_comment'))
        self.assertEqual(request_method.call_args[0],
            ('patch', _('gists/comments/1')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.cs.delete(1)
        self.assertEqual(request_method.call_args[0],
            ('delete', _('gists/comments/1')))
