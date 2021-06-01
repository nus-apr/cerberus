# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class Org(Service):
    """ Consume a `Org Events API
    <http://developer.github.com/v3/events>`_

    """

    def list(self, org=None):
        """ List the events for an Organization

        :param str org: Organization name
        :returns: A :doc:`result`

        """
        request = self.make_request('events.orgs.list', org=org)
        return self._get_normal_result(request)
