# -*- encoding: utf-8 -*-

import requests
from mock import patch

from pygithub3.core.client import Client
from pygithub3.exceptions import ValidationError
from pygithub3.services.users import User, Emails, Followers, Keys
from pygithub3.tests.utils.base import (dummy_json, mock_response,
    mock_response_result)
from pygithub3.tests.utils.core import TestCase
from pygithub3.tests.utils.services import _


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestUserService(TestCase):

    def setUp(self):
        self.us = User()

    def test_GET_without_user(self, request_method):
        request_method.return_value = mock_response()
        self.us.get()
        self.assertEqual(request_method.call_args[0], ('get', _('user')))

    def test_GET_with_user(self, request_method):
        request_method.return_value = mock_response()
        self.us.get('octocat')
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octocat')))

    def test_UPDATE_with_valid_data(self, request_method):
        request_method.return_value = mock_response('patch')
        self.us.update({'name': 'dummy'})
        self.assertEqual(request_method.call_args[0], ('patch', _('user')))

    def test_UPDATE_without_data(self, request_method):
        self.assertRaises(ValidationError, self.us.update, {})


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestEmailsService(TestCase):

    def setUp(self):
        self.es = Emails()

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.es.list().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('user/emails')))

    def test_ADD_without_emails(self, request_method):
        self.assertRaises(ValidationError, self.es.add)
        self.assertFalse(request_method.called)

    def test_ADD_with_emails(self, request_method):
        request_method.return_value = mock_response('post')
        self.es.add('test@example.com', 'test2@example.com')
        self.assertEqual(request_method.call_args[0],
                         ('post', _('user/emails')))

    @patch.object(Client, 'request')
    def test_ADD_filter_emails(self, client_request, dummy):
        client_request.return_value = mock_response('post')
        self.es.add('invalidemail.com', 'inva@lid@xam.com', 'test@xample.com')
        self.assertEqual(client_request.call_args[1],
                         dict(data=('test@xample.com', )))

    def test_DELETE_with_emails(self, request_method):
        request_method.return_value = mock_response('delete')
        self.es.delete('email_must_be_founded')  # or 404 raises
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('user/emails')))

    def test_DELETE_without_emails(self, request_method):
        self.assertRaises(ValidationError, self.es.delete)


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestFollowersService(TestCase):

    def setUp(self):
        self.fs = Followers()

    def test_LIST_without_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.fs.list().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('user/followers')))

    def test_LIST_with_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.fs.list('octocat').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octocat/followers')))

    def test_LIST_FOLLOWING_without_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.fs.list_following().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('user/following')))

    def test_LIST_FOLLOWING_with_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.fs.list_following('octocat').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octocat/following')))

    def test_IS_FOLLOWING(self, request_method):
        self.fs.is_following('octocat')
        self.assertEqual(request_method.call_args[0],
                         ('head', _('user/following/octocat')))

    def test_FOLLOW(self, request_method):
        #request_method.return_value = mock_response('put')
        self.fs.follow('octocat')
        self.assertEqual(request_method.call_args[0],
                         ('put', _('user/following/octocat')))

    def test_UNFOLLOW(self, request_method):
        request_method.return_value = mock_response('delete')
        self.fs.unfollow('octocat')
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('user/following/octocat')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestKeysService(TestCase):

    def setUp(self):
        self.ks = Keys()

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.ks.list().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('user/key')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.ks.get(1)
        self.assertEqual(request_method.call_args[0],
                         ('get', _('user/keys/1')))

    def test_ADD_with_required(self, request_method):
        request_method.return_value = mock_response('post')
        self.ks.add({'key': 'ssh-rsa ...', 'title': 'test'})
        self.assertEqual(request_method.call_args[0], ('post', _('user/keys')))

    def test_ADD_without_required(self, request_method):
        self.assertRaises(ValidationError, self.ks.add, {})

    def test_UPDATE_with_required(self, request_method):
        request_method.return_value = mock_response('patch')
        self.ks.update(1, {'key': 'ssh-rsa ...', 'title': 'test'})
        self.assertEqual(request_method.call_args[0],
                         ('patch', _('user/keys/1')))

    def test_UPDATE_without_required(self, request_method):
        self.assertRaises(ValidationError, self.ks.update, 1, {})

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.ks.delete(1)
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('user/keys/1')))
