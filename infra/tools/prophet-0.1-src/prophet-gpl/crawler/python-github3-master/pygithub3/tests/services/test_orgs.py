# -*- encoding: utf-8 -*-

import requests
from mock import patch

from pygithub3.services.orgs import Org, Members, Teams
from pygithub3.tests.utils.base import (dummy_json, mock_response,
    mock_response_result)
from pygithub3.tests.utils.core import TestCase
from pygithub3.tests.utils.services import _


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestOrgService(TestCase):
    def setUp(self):
        self.org = Org()

    def test_LIST_without_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.org.list().all()
        self.assertEqual(request_method.call_args[0], ('get', _('user/orgs')))

    def test_LIST_with_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.org.list('octocat').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octocat/orgs')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.org.get('acme')
        self.assertEqual(request_method.call_args[0], ('get', _('orgs/acme')))

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response('patch')
        self.org.update('acme', {'company': 'ACME Widgets'})
        self.assertEqual(request_method.call_args[0],
                         ('patch', _('orgs/acme')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestMemberService(TestCase):
    def setUp(self):
        self.ms = Members()

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.ms.list('acme').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('orgs/acme/members')))

    def test_IS_MEMBER(self, request_method):
        request_method.return_value = mock_response()
        self.ms.is_member('acme', 'octocat')
        self.assertEqual(request_method.call_args[0],
                         ('head', _('orgs/acme/members/octocat')))

    def test_REMOVE_MEMBER(self, request_method):
        request_method.return_value = mock_response('delete')
        self.ms.remove_member('acme', 'octocat')
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('orgs/acme/members/octocat')))

    def test_LIST_PUBLIC(self, request_method):
        request_method.return_value = mock_response_result()
        self.ms.list_public('acme').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('orgs/acme/public_members')))

    def test_IS_PUBLIC_MEMBER(self, request_method):
        request_method.return_value = mock_response()
        self.ms.is_public_member('acme', 'octocat')
        self.assertEqual(request_method.call_args[0],
                         ('head', _('orgs/acme/public_members/octocat')))

    def test_PUBLICIZE_MEMBERSHIP(self, request_method):
        request_method.return_value = mock_response()
        self.ms.publicize_membership('acme', 'octocat')
        self.assertEqual(request_method.call_args[0],
                         ('put', _('orgs/acme/public_members/octocat')))

    def test_CONCEAL_MEMBERSHIP(self, request_method):
        request_method.return_value = mock_response('delete')
        self.ms.conceal_membership('acme', 'octocat')
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('orgs/acme/public_members/octocat')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestTeamsService(TestCase):
    def setUp(self):
        self.ts = Teams()

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.ts.list('acme').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('orgs/acme/teams')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response_result()
        self.ts.get(1)
        self.assertEqual(request_method.call_args[0], ('get', _('teams/1')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response_result('post')
        self.ts.create('acme', dict(name='new'))
        self.assertEqual(request_method.call_args[0],
                         ('post', _('orgs/acme/teams')))

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response_result()
        self.ts.update(1, dict(name='edited'))
        self.assertEqual(request_method.call_args[0], ('patch', _('teams/1')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response_result('delete')
        self.ts.delete(1)
        self.assertEqual(request_method.call_args[0], ('delete', _('teams/1')))

    def test_LIST_MEMBERS(self, request_method):
        request_method.return_value = mock_response_result()
        self.ts.list_members(1).all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('teams/1/members')))

    def test_IS_MEMBER(self, request_method):
        request_method.return_value = mock_response_result()
        self.ts.is_member(1, 'octocat')
        self.assertEqual(request_method.call_args[0],
                         ('head', _('teams/1/members/octocat')))

    def test_ADD_MEMBER(self, request_method):
        request_method.return_value = mock_response_result()
        self.ts.add_member(1, 'octocat')
        self.assertEqual(request_method.call_args[0],
                         ('put', _('teams/1/members/octocat')))

    def test_REMOVE_MEMBER(self, request_method):
        request_method.return_value = mock_response_result('delete')
        self.ts.remove_member(1, 'octocat')
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('teams/1/members/octocat')))

    def test_LIST_REPOS(self, request_method):
        request_method.return_value = mock_response_result()
        self.ts.list_repos(1).all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('teams/1/repos')))

    def test_CONTAINS_REPO(self, request_method):
        request_method.return_value = mock_response_result()
        self.ts.contains_repo(1, 'octocat', 're_oct')
        self.assertEqual(request_method.call_args[0],
                         ('head', _('teams/1/repos/octocat/re_oct')))

    def test_ADD_TEAM_REPO(self, request_method):
        request_method.return_value = mock_response_result()
        self.ts.add_repo(1, 'octocat', 're_oct')
        self.assertEqual(request_method.call_args[0],
                         ('put', _('teams/1/repos/octocat/re_oct')))

    def test_REMOVE_TEAM_REPO(self, request_method):
        request_method.return_value = mock_response_result('delete')
        self.ts.remove_repo(1, 'octocat', 're_oct')
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('teams/1/repos/octocat/re_oct')))
