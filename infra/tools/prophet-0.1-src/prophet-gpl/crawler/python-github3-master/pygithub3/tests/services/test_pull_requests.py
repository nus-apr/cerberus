# -*- encoding: utf-8 -*-

import requests
from mock import patch
from nose.tools import raises

from pygithub3.requests.base import ValidationError
from pygithub3.services.pull_requests import PullRequests, Comments
from pygithub3.tests.utils.base import (dummy_json, mock_response,
    mock_response_result)
from pygithub3.tests.utils.core import TestCase
from pygithub3.tests.utils.services import _


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestPullRequestsService(TestCase):
    def setUp(self):
        self.service = PullRequests(user='user', repo='repo')

    def test_LIST(self, reqm):
        reqm.return_value = mock_response_result()
        self.service.list().all()
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/pulls'))
        )

    def test_GET(self, reqm):
        reqm.return_value = mock_response()
        self.service.get(123)
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/pulls/123'))
        )

    def test_CREATE_with_title_and_body(self, reqm):
        reqm.return_value = mock_response('post')
        data = {
            'title': 'this is a pull request',
            'body': 'merge me!',
            'head': 'octocat:some-feature',
            'base': 'master',
        }
        self.service.create(data)
        self.assertEqual(
            reqm.call_args[0],
            ('post', _('repos/user/repo/pulls'))
        )

    def test_CREATE_with_issue(self, reqm):
        reqm.return_value = mock_response('post')
        data = {
            'issue': 1,
            'head': 'octocat:some-feature',
            'base': 'master',
        }
        self.service.create(data)
        self.assertEqual(
            reqm.call_args[0],
            ('post', _('repos/user/repo/pulls'))
        )

    @raises(ValidationError)
    def test_CREATE_with_no_title(self, reqm):
        reqm.return_value = mock_response('post')
        data = {
            'body': 'merge me!',
            'head': 'octocat:some-feature',
            'base': 'master',
        }
        self.service.create(data)

    def test_UPDATE(self, reqm):
        reqm.return_value = mock_response('patch')
        data = {}
        self.service.update(123, data)
        self.assertEqual(
            reqm.call_args[0],
            ('patch', _('repos/user/repo/pulls/123'))
        )

    @raises(ValidationError)
    def test_UPDATE_with_invalid_state(self, reqm):
        reqm.return_value = mock_response('patch')
        data = {'state': 'Illinois'}
        self.service.update(123, data)

    def test_LIST_COMMITS(self, reqm):
        reqm.return_value = mock_response_result('get')
        self.service.list_commits(123).all()
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/pulls/123/commits'))
        )

    def test_LIST_FILES(self, reqm):
        reqm.return_value = mock_response_result('get')
        self.service.list_files(123).all()
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/pulls/123/files'))
        )

    def test_IS_MERGED(self, reqm):
        resp = self.service.is_merged(123)
        self.assertTrue(resp)
        self.assertEqual(
            reqm.call_args[0],
            ('head', _('repos/user/repo/pulls/123/merge'))
        )

    def test_MERGE(self, reqm):
        reqm.return_value = mock_response(200)
        self.service.merge(123, 'merging this')
        self.assertEqual(
            reqm.call_args[0],
            ('put', _('repos/user/repo/pulls/123/merge'))
        )


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestPullRequestCommentsService(TestCase):
    def setUp(self):
        self.service = Comments(user='user', repo='repo')

    def test_LIST(self, reqm):
        reqm.return_value = mock_response_result(200)
        self.service.list(123).all()
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/pulls/123/comments'))
        )

    def test_GET(self, reqm):
        reqm.return_value = mock_response(200)
        self.service.get(1)
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/pulls/comments/1'))
        )

    def test_CREATE(self, reqm):
        reqm.return_value = mock_response(201)
        data = {
            'body': ':sparkles:',
            'commit_id': 'abc123',
            'path': 'foo.txt',
            'position': '2',
        }
        self.service.create(1, data)
        self.assertEqual(
            reqm.call_args[0],
            ('post', _('repos/user/repo/pulls/1/comments'))
        )

    def test_CREATE_in_reply_to(self, reqm):
        reqm.return_value = mock_response(201)
        data = {
            'body': ':sparkles:',
            'in_reply_to': '5',
        }
        self.service.create(1, data)
        self.assertEqual(
            reqm.call_args[0],
            ('post', _('repos/user/repo/pulls/1/comments'))
        )

    def test_UPDATE(self, reqm):
        reqm.return_value = mock_response(200)
        data = {
            'body': 'something completely different',
        }
        self.service.update(1, data)
        self.assertEqual(
            reqm.call_args[0],
            ('patch', _('repos/user/repo/pulls/comments/1'))
        )

    def test_DELETE(self, reqm):
        reqm.return_value = mock_response(204)
        self.service.delete(1)
        self.assertEqual(
            reqm.call_args[0],
            ('delete', _('repos/user/repo/pulls/comments/1'))
        )
