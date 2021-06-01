# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class Repo(Service):
    """ Consume `Repo Events API
    <http://developer.github.com/v3/events/#list-repository-events>`_

    """

    def list(self, user=None, repo=None):
        """ Get repository's events

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`

        .. note::
            Remember that the Events API give 10 pages with 30 entries, up to
            300 events, so you'll only get the last 300 Repo events
        """
        request = self.make_request('events.repos.list', user=user, repo=repo)
        return self._get_normal_result(request)
