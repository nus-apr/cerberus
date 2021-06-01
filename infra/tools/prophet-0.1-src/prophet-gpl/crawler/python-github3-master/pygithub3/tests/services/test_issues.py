# -*- encoding: utf-8 -*-

import requests
from mock import patch

from pygithub3.exceptions import ValidationError
from pygithub3.services.issues import (Issue, Comments, Events, Labels,
    Milestones)
from pygithub3.tests.utils.base import (dummy_json, mock_response,
    mock_response_result)
from pygithub3.tests.utils.core import TestCase
from pygithub3.tests.utils.services import _


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestIssuesService(TestCase):

    def setUp(self):
        self.isu = Issue(user='octocat', repo='Hello-World')

    def test_LIST_without_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.isu.list().all()
        self.assertEqual(request_method.call_args[0], ('get', _('issues')))

    def test_LIST_by_repo(self, request_method):
        request_method.return_value = mock_response_result()
        self.isu.list_by_repo().all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/issues')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.isu.get(1)
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/issues/1')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.isu.create(dict(title='My issue', body='Fix this issue'))
        self.assertEqual(request_method.call_args[0],
            ('post', _('repos/octocat/Hello-World/issues')))

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response('patch')
        self.isu.update(1, {'body': 'edited'})
        self.assertEqual(request_method.call_args[0],
            ('patch', _('repos/octocat/Hello-World/issues/1')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestCommentService(TestCase):

    def setUp(self):
        self.cs = Comments(user='octocat', repo='Hello-World')

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.cs.list(1).all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/issues/1/comments')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.cs.get(1)
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/issues/comments/1')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.cs.create(1, 'comment')
        self.assertEqual(request_method.call_args[0],
            ('post', _('repos/octocat/Hello-World/issues/1/comments')))

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response('patch')
        self.cs.update(1, 'new comment')
        self.assertEqual(request_method.call_args[0],
            ('patch', _('repos/octocat/Hello-World/issues/comments/1')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.cs.delete(1)
        self.assertEqual(request_method.call_args[0],
            ('delete', _('repos/octocat/Hello-World/issues/comments/1')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestEventsService(TestCase):

    def setUp(self):
        self.ev = Events(user='octocat', repo='Hello-World')

    def test_LIST_by_issue(self, request_method):
        request_method.return_value = mock_response_result()
        self.ev.list_by_issue(1).all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/issues/1/events')))

    def test_LIST_by_repo(self, request_method):
        request_method.return_value = mock_response_result()
        self.ev.list_by_repo().all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/issues/events')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.ev.get(1)
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/issues/events/1')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestLabelsService(TestCase):

    def setUp(self):
        self.lb = Labels(user='octocat', repo='Hello-World')

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.lb.get('bug')
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/labels/bug')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.lb.create(dict(name='bug', color='FF0000'))
        self.assertEqual(request_method.call_args[0],
            ('post', _('repos/octocat/Hello-World/labels')))

    def test_CREATE_with_invalid_color(self, request_method):
        request_method.return_value = mock_response('post')
        # invalid color
        with self.assertRaises(ValidationError):
            args = {'name': 'bug', 'color': 'FF00'}
            self.lb.create(args)

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response('patch')
        self.lb.update('bug', dict(name='critical', color='FF0000'))
        self.assertEqual(request_method.call_args[0],
            ('patch', _('repos/octocat/Hello-World/labels/bug')))

    def test_UPDATE_with_invalid_color(self, request_method):
        request_method.return_value = mock_response('post')
        # invalid color
        with self.assertRaises(ValidationError):
            args = {'name': 'critical', 'color': 'FF00'}
            self.lb.update('bug', args)

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.lb.delete('bug')
        self.assertEqual(request_method.call_args[0],
            ('delete', _('repos/octocat/Hello-World/labels/bug')))

    def test_LIST_by_issue(self, request_method):
        request_method.return_value = mock_response()
        self.lb.list_by_issue(1)
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/issues/1/labels')))

    def test_ADD_to_issue(self, request_method):
        request_method.return_value = mock_response('post')
        self.lb.add_to_issue(1, ('bug', 'critical'))
        self.assertEqual(request_method.call_args[0],
            ('post', _('repos/octocat/Hello-World/issues/1/labels')))

    def test_REMOVE_from_issue(self, request_method):
        request_method.return_value = mock_response('delete')
        self.lb.remove_from_issue(1, 'bug')
        self.assertEqual(request_method.call_args[0],
            ('delete', _('repos/octocat/Hello-World/issues/1/labels/bug')))

    def test_REPLACE_all(self, request_method):
        request_method.return_value = mock_response()
        self.lb.replace_all(1, ['bug', 'critical'])
        self.assertEqual(request_method.call_args[0],
            ('put', _('repos/octocat/Hello-World/issues/1/labels')))

    def test_REMOVE_all(self, request_method):
        request_method.return_value = mock_response('delete')
        self.lb.remove_all(1)
        self.assertEqual(request_method.call_args[0],
            ('delete', _('repos/octocat/Hello-World/issues/1/labels')))

    def test_LIST_by_milestone(self, request_method):
        request_method.return_value = mock_response_result()
        self.lb.list_by_milestone(1).all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/milestones/1/labels')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestMilestonesService(TestCase):

    def setUp(self):
        self.mi = Milestones(user='octocat', repo='Hello-World')

    def test_LIST_by_repo(self, request_method):
        request_method.return_value = mock_response_result()
        self.mi.list().all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/milestones')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.mi.get(1)
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/Hello-World/milestones/1')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.mi.create(dict(title='test'))
        self.assertEqual(request_method.call_args[0],
            ('post', _('repos/octocat/Hello-World/milestones')))

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response('patch')
        self.mi.update(1, dict(title='test'))
        self.assertEqual(request_method.call_args[0],
            ('patch', _('repos/octocat/Hello-World/milestones/1')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.mi.delete(1)
        self.assertEqual(request_method.call_args[0],
            ('delete', _('repos/octocat/Hello-World/milestones/1')))
