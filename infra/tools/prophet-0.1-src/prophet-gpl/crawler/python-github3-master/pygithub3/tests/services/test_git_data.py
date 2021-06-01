# -*- encoding: utf-8 -*-

import requests
from mock import patch

from pygithub3.services.git_data import (Blobs, Commits, References, Tags,
    Trees)
from pygithub3.tests.utils.base import (dummy_json, mock_response,
    mock_response_result)
from pygithub3.tests.utils.core import TestCase
from pygithub3.tests.utils.services import _


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestBlobsService(TestCase):
    def setUp(self):
        self.service = Blobs(user='octocat', repo='repo')

    def test_GET(self, reqm):
        reqm.return_value = mock_response()
        self.service.get('abc123')
        self.assertEqual(reqm.call_args[0],
                         ('get', _('repos/octocat/repo/git/blobs/abc123')))

    def test_CREATE(self, reqm):
        reqm.return_value = mock_response('post')
        self.service.create({'content': 'hello, friends', 'encoding':
                             'utf-8'})
        self.assertEqual(reqm.call_args[0],
                         ('post', _('repos/octocat/repo/git/blobs')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestCommitsService(TestCase):
    def setUp(self):
        self.service = Commits(user='octocat', repo='repo')

    def test_GET(self, reqm):
        reqm.return_value = mock_response()
        self.service.get('abc123')
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/octocat/repo/git/commits/abc123'))
        )

    def test_CREATE(self, reqm):
        reqm.return_value = mock_response('post')
        self.service.create({
            'message': 'hello',
            'tree': 'abc123',
            'parents': ['mom', 'dad'],
        })
        self.assertEqual(
            reqm.call_args[0],
            ('post', _('repos/octocat/repo/git/commits'))
        )


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestReferencesService(TestCase):
    def setUp(self):
        self.service = References(user='user', repo='repo')

    def test_GET(self, reqm):
        reqm.return_value = mock_response()
        self.service.get('heads/fnord')
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/git/refs/heads/fnord'))
        )

    def test_LIST(self, reqm):
        reqm.return_value = mock_response_result()
        self.service.list().all()
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/git/refs'))
        )

    def test_create(self, reqm):
        reqm.return_value = mock_response('post')
        self.service.create({'sha': 'hello', 'ref': 'something'})
        self.assertEqual(
            reqm.call_args[0],
            ('post', _('repos/user/repo/git/refs'))
        )

    def test_update(self, reqm):
        reqm.return_value = mock_response('patch')
        self.service.update('master', {'sha': 'abc123'})
        self.assertEqual(
            reqm.call_args[0],
            ('patch', _('repos/user/repo/git/refs/master'))
        )

    def test_delete(self, reqm):
        reqm.return_value = mock_response('delete')
        self.service.delete('branch')
        self.assertEqual(
            reqm.call_args[0],
            ('delete', _('repos/user/repo/git/refs/branch'))
        )


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestTagsService(TestCase):
    def setUp(self):
        self.service = Tags(user='user', repo='repo')

    def test_GET(self, reqm):
        reqm.return_value = mock_response()
        self.service.get('abc123')
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/git/tags/abc123'))
        )

    def test_CREATE(self, reqm):
        reqm.return_value = mock_response('post')
        self.service.create({'tag': 'v1.2.3', 'message': 'a tag',
                             'object': 'abc123', 'type': 'commit'})
        self.assertEqual(
            reqm.call_args[0],
            ('post', _('repos/user/repo/git/tags'))
        )


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestTreesService(TestCase):
    def setUp(self):
        self.service = Trees(user='user', repo='repo')

    def test_GET(self, reqm):
        reqm.return_value = mock_response()
        self.service.get('abc123')
        self.assertEqual(
            reqm.call_args[0],
            ('get', _('repos/user/repo/git/trees/abc123'))
        )

    def test_CREATE(self, reqm):
        reqm.return_value = mock_response('post')
        self.service.create({
            'tree': [
                {'path': 'foo.txt', 'mode': '100644', 'type': 'blob',
                 'sha': 'abc123'},
            ],
        })
        self.assertEqual(
            reqm.call_args[0],
            ('post', _('repos/user/repo/git/trees'))
        )
