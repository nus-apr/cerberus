# -*- encoding: utf-8 -*-

import requests
from mock import patch

from pygithub3.tests.utils.core import TestCase
from pygithub3.services.events import Event
from pygithub3.tests.utils.base import (mock_response_result, dummy_json)
from pygithub3.tests.utils.services import _


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestEventsService(TestCase):

    def setUp(self):
        self.events = Event()

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.events.list().all()
        self.assertEqual(request_method.call_args[0], ('get', _('events')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestRepoEventsService(TestCase):

    def setUp(self):
        self.events = Event()

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.events.repos.list(user='octocat', repo='octocat_repo').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/octocat/octocat_repo/events')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestNetworkEventsService(TestCase):

    def setUp(self):
        self.events = Event()

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.events.networks.list(user='octocat', repo='octocat_repo').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('networks/octocat/octocat_repo/events')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestOrgsEventsService(TestCase):

    def setUp(self):
        self.events = Event()

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.events.orgs.list(org='acme').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('orgs/acme/events')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestUserEventsService(TestCase):

    def setUp(self):
        self.events = Event()

    def test_LIST_received(self, request_method):
        request_method.return_value = mock_response_result()
        self.events.users.list_received(user='octocat').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octocat/received_events')))

    def test_LIST_received_public(self, request_method):
        request_method.return_value = mock_response_result()
        self.events.users.list_received_public(user='octocat').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octocat/received_events/public')))

    def test_LIST_performed(self, request_method):
        request_method.return_value = mock_response_result()
        self.events.users.list_performed(user='octocat').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octocat/events')))

    def test_LIST_performed_public(self, request_method):
        request_method.return_value = mock_response_result()
        self.events.users.list_performed_public(user='octocat').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octocat/events/public')))

    def test_LIST_orgs(self, request_method):
        request_method.return_value = mock_response_result()
        self.events.users.orgs(user='octocat', org='acme').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octocat/events/orgs/acme')))
