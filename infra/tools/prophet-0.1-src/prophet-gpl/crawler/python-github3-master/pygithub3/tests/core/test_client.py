# -*- encoding: utf-8 -*-

import requests

from mock import patch

from pygithub3.core.client import Client
from pygithub3.exceptions import NotFound, BadRequest, UnprocessableEntity
from pygithub3.github import Github
from pygithub3.tests.utils.base import mock_response
from pygithub3.tests.utils.core import TestCase


class TestClient(TestCase):

    def setUp(self):
        self.c = Client()

    def test_set_credentials_with_valid(self):
        self.c.set_credentials('login', 'password')
        self.assertEqual(self.c.requester.auth, ('login', 'password'))

    def test_set_credentials_with_invalid(self):
        self.c.set_credentials('', '')
        self.assertIsNone(self.c.requester.auth)

    def test_set_token_with_valid(self):
        self.c.set_token('tokenize')
        self.assertEqual(dict(self.c.requester.params)['access_token'],
            'tokenize')

    def test_set_token_with_invalid(self):
        self.c.set_token('')
        self.assertIsNone(dict(self.c.requester.params).get('access_token'))

    def test_INIT_client_with_another_config_args(self):
        new_c = Client(base_url='url', per_page=10, user='me', repo='myrepo',
                       verbose='stream')
        self.assertEqual(new_c.config['base_url'], 'url')
        self.assertEqual(dict(new_c.requester.params)['per_page'], 10)
        self.assertEqual(new_c.user, 'me')
        self.assertEqual(new_c.repo, 'myrepo')
        self.assertEqual(new_c.requester.config['verbose'], 'stream')

    @patch.object(requests.sessions.Session, 'request')
    def test_PARSE_args_in_request_without_params(self, request_method):
        extra = dict(arg1='arg1', arg2='arg2')
        self.c.request('', '', data='data', **extra)
        request_method.assert_called_with('', self.c.config['base_url'],
            data='data', params=extra)

    @patch.object(requests.sessions.Session, 'request')
    def test_PARSE_args_in_request_with_params(self, request_method):
        extra = dict(arg1='arg1', arg2='arg2')
        self.c.request('', '', params=dict(arg0='arg0'), **extra)
        request_method.assert_called_with('', self.c.config['base_url'],
            params=dict(arg0='arg0', **extra))

    @patch.object(Client, 'request')
    def test_DELEGATES_methods(self, request_method):
        request_method.return_value = mock_response()
        self.c.get('')
        request_method.assert_called_with('get', '')

        request_method.return_value = mock_response('post')
        self.c.post('')
        request_method.assert_called_with('post', '')

        request_method.return_value = mock_response('patch')
        self.c.patch('')
        request_method.assert_called_with('patch', '')

        self.c.put('')
        request_method.assert_called_with('put', '')

        request_method.return_value = mock_response('delete')
        self.c.delete('')
        request_method.assert_called_with('delete', '')

        self.c.head('')
        request_method.assert_called_with('head', '')


@patch.object(requests.sessions.Session, 'request')
class TestClientRaises(TestCase):

    def setUp(self):
        self.c = Client()
        self.callback = (self.c.request, 'method', 'request')

    def test_raise_NotFound(self, request_method):
        request_method.return_value.status_code = 404
        self.assertRaises(NotFound, *self.callback)

    def test_raise_BadRequest(self, request_method):
        request_method.return_value.status_code = 400
        self.assertRaises(BadRequest, *self.callback)

    def test_raise_UnprocessableEntity(self, request_method):
        request_method.return_value.status_code = 422
        request_method.return_value.content = {}
        self.assertRaises(UnprocessableEntity, *self.callback)

class TestGithubGlue(TestCase):

    def test_init(self):
        gh = Github(login='dummy', password='dummy', user='dummy',
            repo='dummy')
        self.assertTrue(getattr(gh, '_users', False))
        self.assertTrue(getattr(gh, '_repos', False))
        self.assertTrue(getattr(gh, '_gists', False))
        self.assertTrue(getattr(gh, '_git_data', False))
        self.assertTrue(getattr(gh, '_pull_requests', False))
        self.assertTrue(getattr(gh, '_orgs', False))
        self.assertTrue(getattr(gh, '_issues', False))
        self.assertTrue(getattr(gh, '_events', False))
