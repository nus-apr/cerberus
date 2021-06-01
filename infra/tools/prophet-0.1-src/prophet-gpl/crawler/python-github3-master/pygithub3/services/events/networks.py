# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class Network(Service):
    """ Consume a Repo's public `Network Events API
    <http://developer.github.com/v3/events>`_

    """

    def list(self, user=None, repo=None):
        """ List the events for a repository's Network

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('events.networks.list',
                                    user=user, repo=repo)
        return self._get_normal_result(request)
