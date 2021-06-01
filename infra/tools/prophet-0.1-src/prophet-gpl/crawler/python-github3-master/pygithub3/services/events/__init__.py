# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service
from pygithub3.services import issues
from pygithub3.services.events import networks, orgs, repos, users


class Event(Service):
    """ Consume `Events API <http://developer.github.com/v3/events>`_

    The events API supports pagination, but with a fixed page size of 30; In
    addition, fetching up to ten pages is supported, for a total of 300 events.
    """

    def __init__(self, **config):
        self.issues = issues.events.Events(**config)
        self.networks = networks.Network(**config)
        self.orgs = orgs.Org(**config)
        self.repos = repos.Repo(**config)
        self.users = users.User(**config)
        super(Event, self).__init__(**config)

    def list(self):
        """ List all public events.

        :returns: A :doc:`result`

        .. note::
            Hits the API fetching maximum number of events (300 = 30/page * 10)
        """

        """ TODO
            This method uses ``_get_normal_result`` which hits the API fetching
            maximum number of events (300 = 30/page * 10).

            If there's a good way to tell ``smart.Method`` about the last page
            ahead of time, that may be a better way to proceed. Otherwise it
            tries to set that via ``_set_last_page_from`` which fails because
            that data is not in the returned header.
        """
        request = self.request_builder('events.list')
        return self._get_normal_result(request, per_page=None)
