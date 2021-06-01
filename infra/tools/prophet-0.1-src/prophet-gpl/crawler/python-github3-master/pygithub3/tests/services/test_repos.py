# -*- encoding: utf-8 -*-

import requests
from mock import patch

from pygithub3.services.repos import (Repo, Collaborators, Commits, Downloads,
    Forks, Keys, Watchers, Hooks)
from pygithub3.tests.utils.base import (dummy_json, mock_response,
    mock_response_result)
from pygithub3.tests.utils.core import TestCase
from pygithub3.tests.utils.services import _


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestRepoService(TestCase):

    def setUp(self):
        self.rs = Repo()
        self.rs.set_user('octocat')
        self.rs.set_repo('octocat_repo')

    def test_LIST_without_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.set_user('')
        self.rs.list().all()
        self.assertEqual(request_method.call_args[0], ('get', _('user/repos')))

    def test_LIST_with_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.list('octoc').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octoc/repos')))

    def test_LIST_filters(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.list('octoc', type='public').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('users/octoc/repos')))
        self.assertEqual(request_method.call_args[1]['params']['type'],
                         'public')

    def test_LIST_BY_ORG(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.list_by_org('org_name').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('orgs/org_name/repos')))

    def test_LIST_BY_ORG_filters(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.list_by_org('org_name', type='public').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('orgs/org_name/repos')))
        self.assertEqual(request_method.call_args[1]['params']['type'],
                         'public')

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.rs.create({'name': 'test'})
        self.assertEqual(request_method.call_args[0],
                         ('post', _('user/repos')))

    def test_CREATE_in_org(self, request_method):
        request_method.return_value = mock_response('post')
        self.rs.create({'name': 'test'}, in_org='org_name')
        self.assertEqual(request_method.call_args[0],
                         ('post', _('orgs/org_name/repos')))

    def test_GET_with_repo_in_args(self, request_method):
        request_method.return_value = mock_response()
        self.rs.get(user='user', repo='repo')
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/user/repo')))

    def test_GET_with_repo_in_service(self, request_method):
        request_method.return_value = mock_response()
        self.rs.get()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/octocat/octocat_repo')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.rs.delete()
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('repos/octocat/octocat_repo')))

    def test_UPDATE_with_repo_in_args(self, request_method):
        request_method.return_value = mock_response('patch')
        self.rs.update({'name': 'test'}, user='user', repo='repo')
        self.assertEqual(request_method.call_args[0],
                         ('patch', _('repos/user/repo')))

    def test_UPDATE_with_repo_in_service(self, request_method):
        request_method.return_value = mock_response('patch')
        self.rs.update({'name': 'test'})
        self.assertEqual(request_method.call_args[0],
                         ('patch', _('repos/octocat/octocat_repo')))

    """ From here I stop to do '*in_args' and '*filter' tests, I consider
    that I tested it enough... """

    def test_LIST_contributors(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.list_contributors().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/octocat/octocat_repo/contributors')))

    def test_LIST_contributors_with_anonymous(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.list_contributors_with_anonymous().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/octocat/octocat_repo/contributors')))
        self.assertEqual(request_method.call_args[1]['params']['anom'], True)

    def test_LIST_languages(self, request_method):
        request_method.return_value = mock_response()
        self.rs.list_languages()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/octocat/octocat_repo/languages')))

    def test_LIST_teams(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.list_teams().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/octocat/octocat_repo/teams')))

    def test_LIST_tags(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.list_tags().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/octocat/octocat_repo/tags')))

    def test_LIST_branches(self, request_method):
        request_method.return_value = mock_response_result()
        self.rs.list_branches().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/octocat/octocat_repo/branches')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestCollaboratorsService(TestCase):

    def setUp(self):
        self.cs = Collaborators()
        self.cs.set_user('octocat')
        self.cs.set_repo('oc_repo')

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.cs.list().all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/octocat/oc_repo/collaborators')))

    def test_IS_colaborator(self, request_method):
        request_method.return_value = mock_response()
        self.cs.is_collaborator('user')
        self.assertEqual(request_method.call_args[0],
            ('head', _('repos/octocat/oc_repo/collaborators/user')))

    def test_ADD(self, request_method):
        self.cs.add('user')
        self.assertEqual(request_method.call_args[0],
            ('put', _('repos/octocat/oc_repo/collaborators/user')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.cs.delete('user')
        self.assertEqual(request_method.call_args[0],
            ('delete', _('repos/octocat/oc_repo/collaborators/user')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestCommitsService(TestCase):

    def setUp(self):
        self.cs = Commits(user='oct', repo='re_oct')

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.cs.list().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/commits')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.cs.get('e3bc')
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/commits/e3bc')))

    def test_LIST_comments(self, request_method):
        request_method.return_value = mock_response_result()
        self.cs.list_comments().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/comments')))

    def test_LIST_comments_for_commit(self, request_method):
        request_method.return_value = mock_response_result()
        self.cs.list_comments(sha='e3bc').all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/commits/e3bc/comments')))

    def test_CREATE_comment(self, request_method):
        request_method.return_value = mock_response('post')
        data = dict(body='some', commit_id='e2bc',
                    line=1, path='some.txt', position=1)
        self.cs.create_comment(data, 'e3bc')
        self.assertEqual(request_method.call_args[0],
                         ('post', _('repos/oct/re_oct/commits/e3bc/comments')))

    def test_GET_comment(self, request_method):
        request_method.return_value = mock_response()
        self.cs.get_comment(1)
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/comments/1')))

    def test_UPDATE_comment(self, request_method):
        request_method.return_value = mock_response('patch')
        self.cs.update_comment({'body': 'changed'}, 1)
        self.assertEqual(request_method.call_args[0],
                         ('patch', _('repos/oct/re_oct/comments/1')))

    def test_COMPARE(self, request_method):
        request_method.return_value = mock_response()
        self.cs.compare('develop', 'master')
        self.assertEqual(request_method.call_args[0],
                ('get', _('repos/oct/re_oct/compare/develop...master')))

    def test_DELETE_comment(self, request_method):
        request_method.return_value = mock_response('delete')
        self.cs.delete_comment(1)
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('repos/oct/re_oct/comments/1')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestDownloadsService(TestCase):

    def setUp(self):
        self.ds = Downloads(user='oct', repo='re_oct')

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.ds.list().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/downloads')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.ds.get(1)
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/downloads/1')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.ds.delete(1)
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('repos/oct/re_oct/downloads/1')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        download = self.ds.create({'name': 'some', 'size': 100})
        self.assertEqual(request_method.call_args[0],
                         ('post', _('repos/oct/re_oct/downloads')))
        self.assertTrue(hasattr(download, 'upload'))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestForksService(TestCase):

    def setUp(self):
        self.fs = Forks(user='oct', repo='re_oct')

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.fs.list().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/forks')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.fs.create()
        self.assertEqual(request_method.call_args[0],
                         ('post', _('repos/oct/re_oct/forks')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestKeysService(TestCase):

    def setUp(self):
        self.ks = Keys(user='oct', repo='re_oct')

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.ks.list().all()
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/keys')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.ks.get(1)
        self.assertEqual(request_method.call_args[0],
                         ('get', _('repos/oct/re_oct/keys/1')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.ks.create({'title': 'test', 'key': 'ssh-rsa AAA'})
        self.assertEqual(request_method.call_args[0],
                         ('post', _('repos/oct/re_oct/keys')))

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response('patch')
        self.ks.update(1, {'title': 'test', 'key': 'ssh-rsa AAA'})
        self.assertEqual(request_method.call_args[0],
                         ('patch', _('repos/oct/re_oct/keys/1')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.ks.delete(1)
        self.assertEqual(request_method.call_args[0],
                         ('delete', _('repos/oct/re_oct/keys/1')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestWatchersService(TestCase):

    def setUp(self):
        self.ws = Watchers(user='oct', repo='re_oct')

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.ws.list().all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/oct/re_oct/watchers')))

    def test_LIST_repos(self, request_method):
        request_method.return_value = mock_response_result()
        self.ws.list_repos().all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('user/watched')))

    def test_LIST_repos_with_user(self, request_method):
        request_method.return_value = mock_response_result()
        self.ws.list_repos('oct').all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('users/oct/watched')))

    def test_IS_watching(self, request_method):
        request_method.return_value = mock_response()
        self.assertTrue(self.ws.is_watching())
        self.assertEqual(request_method.call_args[0],
            ('head', _('user/watched/oct/re_oct')))

    def test_WATCH(self, request_method):
        self.ws.watch()
        self.assertEqual(request_method.call_args[0],
            ('put', _('user/watched/oct/re_oct')))

    def test_UNWATCH(self, request_method):
        request_method.return_value = mock_response('delete')
        self.ws.unwatch()
        self.assertEqual(request_method.call_args[0],
            ('delete', _('user/watched/oct/re_oct')))


@dummy_json
@patch.object(requests.sessions.Session, 'request')
class TestHooksService(TestCase):

    def setUp(self):
        self.hs = Hooks(user='oct', repo='re_oct')

    def test_LIST(self, request_method):
        request_method.return_value = mock_response_result()
        self.hs.list().all()
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/oct/re_oct/hooks')))

    def test_GET(self, request_method):
        request_method.return_value = mock_response()
        self.hs.get(1)
        self.assertEqual(request_method.call_args[0],
            ('get', _('repos/oct/re_oct/hooks/1')))

    def test_CREATE(self, request_method):
        request_method.return_value = mock_response('post')
        self.hs.create(dict(name='acunote', config={'usr': 'http...'}))
        self.assertEqual(request_method.call_args[0],
            ('post', _('repos/oct/re_oct/hooks')))

    def test_UPDATE(self, request_method):
        request_method.return_value = mock_response('patch')
        self.hs.update(1, dict(events=['push']))
        self.assertEqual(request_method.call_args[0],
            ('patch', _('repos/oct/re_oct/hooks/1')))

    def test_TEST(self, request_method):
        request_method.return_value = mock_response('post')
        self.hs.test(1)
        self.assertEqual(request_method.call_args[0],
            ('post', _('repos/oct/re_oct/hooks/1/test')))

    def test_DELETE(self, request_method):
        request_method.return_value = mock_response('delete')
        self.hs.delete(1)
        self.assertEqual(request_method.call_args[0],
                ('delete', _('repos/oct/re_oct/hooks/1')))
