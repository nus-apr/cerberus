# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service, MimeTypeMixin


class Commits(Service, MimeTypeMixin):
    """ Consume `Commits API
    <http://developer.github.com/v3/repos/commits>`_

    .. note::
        This service support :ref:`mimetypes-section` configuration
    """

    def list(self, user=None, repo=None, sha=None, path=None):
        """ Get repository's commits

        :param str user: Username
        :param str repo: Repository
        :param str sha: Sha or branch to start listing commits from
        :param str path: Only commits containing this file path will be returned
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            Usually a repository has thousand of commits, so be careful when
            consume the result. You should filter with ``sha`` or directly
            clone the repository

        ::

            commits_service.list(user='octocat', repo='oct_repo')
            commits_service.list(user='octocat', repo='oct_repo', sha='dev')
            commits_service.list(user='django', repo='django', sha='master',
                path='django/db/utils.py')
        """
        request = self.make_request('repos.commits.list', user=user, repo=repo)
        params = {}
        params.update(sha and {'sha': sha} or {})
        params.update(path and {'path': path} or {})
        return self._get_normal_result(request, **params)

    def get(self, sha, user=None, repo=None):
        """ Get a single commit

        :param str sha: Commit's sha
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.commits.get',
            sha=sha, user=user, repo=repo)
        return self._get(request)

    def list_comments(self, sha=None, user=None, repo=None):
        """ Get commit's comments

        :param str sha: Commit's sha
        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`

        If you call it without ``sha``, get all commit's comments of a
        repository
        ::

            commits_service.list_comments('6dcb09', user='octocat',
                repo='oct_repo')
            commits_service.list_comments(user='octocat', repo='oct_repo')
        """
        request = self.make_request('repos.commits.list_comments',
            sha=sha, user=user, repo=repo)
        return self._get_result(request, **self._get_mimetype_as_header())

    def create_comment(self, data, sha, user=None, repo=None):
        """ Create a commit comment

        :param dict data: Input. See `github commits doc`_
        :param str sha: Commit's sha
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated

        ::

            data = {
                "body": "Nice change",
                "commit_id": "6dcb09b5b57875f334f61aebed695e2e4193db5e",
                "line": 1,
                "path": "file1.txt",
                "position": 4
            }
            commits_service.create_comment(data, '6dcb09', user='octocat',
                repo='oct_repo')
        """
        request = self.make_request('repos.commits.create_comment',
            sha=sha, user=user, repo=repo, body=data)
        return self._post(request, **self._get_mimetype_as_header())

    def get_comment(self, cid, user=None, repo=None):
        """ Get a single commit comment

        :param int cid: Commit comment id
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.commits.get_comment',
            comment_id=cid, user=user, repo=repo)
        return self._get(request, **self._get_mimetype_as_header())

    def update_comment(self, data, cid, user=None, repo=None):
        """ Update a single commit comment

        :param dict data: Input. See `github commits doc`_
        :param int cid: Commit comment id
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated

        ::

            commits_service.update_comment(dict(body='nice change'), 42,
                user='octocat', repo='oct_repo')
        """
        request = self.make_request('repos.commits.update_comment',
            comment_id=cid, user=user, repo=repo, body=data)
        return self._patch(request, **self._get_mimetype_as_header())

    def compare(self, base, head, user=None, repo=None):
        """ Compare two commits

        :param str base: Base commit sha
        :param str head: Head commit sha
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        ::

            commits_service.compare('6dcb09', 'master', user='octocat',
                repo='oct_repo')
        """
        request = self.make_request('repos.commits.compare',
            base=base, head=head, user=user, repo=repo)
        return self._get(request)

    def delete_comment(self, cid, user=None, repo=None):
        """ Delete a single commit comment

        :param int cid: Commit comment id
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.commits.delete_comment',
            comment_id=cid, user=user, repo=repo)
        self._delete(request)
