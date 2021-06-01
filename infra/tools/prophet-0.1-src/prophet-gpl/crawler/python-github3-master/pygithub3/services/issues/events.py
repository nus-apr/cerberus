# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class Events(Service):
    """ Consume `Issues Events API
    <http://developer.github.com/v3/issues/events>`_ """

    def list_by_issue(self, number, user=None, repo=None):
        """ List events for an issue

        :param int number: Issue number
        :param str user: Username
        :param str repo: Repo name
        :returns: A :doc:`result`
        """
        request = self.make_request('issues.events.list_by_issue',
            user=user, repo=repo, number=number)
        return self._get_result(request)

    def list_by_repo(self, user=None, repo=None):
        """ List events for a repository

        :param str user: Username
        :param str repo: Repo name
        :returns: A :doc:`result`
        """
        request = self.make_request('issues.events.list_by_repo',
            user=user, repo=repo)
        return self._get_result(request)

    def get(self, id, user=None, repo=None):
        """ Get a single event

        :param int id: Comment id
        :param str user: Username
        :param str repo: Repo name
        """
        request = self.make_request('issues.events.get', user=user,
            repo=repo, id=id)
        return self._get(request)
