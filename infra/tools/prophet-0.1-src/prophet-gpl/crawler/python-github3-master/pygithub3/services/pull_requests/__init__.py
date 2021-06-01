# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service, MimeTypeMixin
from .comments import Comments


class PullRequests(Service, MimeTypeMixin):
    """Consume `Pull Request API <http://developer.github.com/v3/pulls/>`_"""

    def __init__(self, **config):
        self.comments = Comments(**config)
        super(PullRequests, self).__init__(**config)

    def list(self, state='open', user=None, repo=None):
        """List all of the pull requests for a repo

        :param str state: Pull requests state ('open' or 'closed')
        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        return self._get_result(
            self.make_request('pull_requests.list', user=user, repo=repo),
            state=state
        )

    def get(self, number, user=None, repo=None):
        """Get a single pull request

        :param str number: The number of the pull request to get
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        return self._get(
            self.make_request('pull_requests.get', number=number, user=user,
                              repo=repo)
        )

    def create(self, data, user=None, repo=None):
        """Create a pull request

        :param dict data: Input. See `github pullrequests doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        return self._post(
            self.make_request('pull_requests.create', body=data, user=user,
                              repo=repo)
        )

    def update(self, number, data, user=None, repo=None):
        """Update a pull request

        :param str number: The number of the the pull request to update
        :param dict data: Input. See `github pullrequests doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        return self._patch(
            self.make_request('pull_requests.update', number=number,
                              body=data, user=user, repo=repo)
        )

    def list_commits(self, number, user=None, repo=None):
        """List the commits for a pull request

        :param str number: The number of the pull request to list commits for
        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        return self._get_result(
            self.make_request('pull_requests.list_commits', number=number,
                              user=user, repo=repo)
        )

    def list_files(self, number, user=None, repo=None):
        """List the files for a pull request

        :param str number: The number of the pull request to list files for
        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        return self._get_result(
            self.make_request('pull_requests.list_files', number=number,
                              user=user, repo=repo)
        )

    def is_merged(self, number, user=None, repo=None):
        """Gets whether a pull request has been merged or not.

        :param str number: The pull request to check
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        return self._bool(
            self.make_request('pull_requests.is_merged', number=number,
                              user=user, repo=repo)
        )

    def merge(self, number, message='', user=None, repo=None):
        """Merge a pull request.

        :param str number: The pull request to merge
        :param str message: Message of pull request
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        This currently raises an HTTP 405 error if the request is not
        mergable.

        """
        body = {'commit_message': message}
        return self._put(
            self.make_request('pull_requests.merge', number=number,
                              body=body, user=user, repo=repo)
        )
