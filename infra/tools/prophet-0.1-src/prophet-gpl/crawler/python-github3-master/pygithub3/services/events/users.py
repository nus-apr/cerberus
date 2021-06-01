# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class User(Service):
    """ Consume `User Events API
    <http://developer.github.com/v3/events>`_

    """

    def list_received(self, user=None):
        """ List the events received by a given user. If authenticated as the
        given user, you'll see private events as well as public events.

        :param str user: Username
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('events.users.list_received', user=user)
        return self._get_normal_result(request)

    def list_received_public(self, user=None):
        """ List only the public events received by the given user.

        :param str user: Username
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('events.users.list_received_public',
                                    user=user)
        return self._get_normal_result(request)

    def list_performed(self, user=None):
        """ List the events performed by a given user. If authenticated as the
        given user, you'll see private events as well as public events.

        :param str user: Username
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('events.users.list_performed', user=user)
        return self._get_normal_result(request)

    def list_performed_public(self, user=None):
        """ List only the public events performed by the given user.

        :param str user: Username
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('events.users.list_performed_public',
                                    user=user)
        return self._get_normal_result(request)

    def orgs(self, user=None, org=None):
        """ List the events for the User's organization dashboard.

        :param str user: Username
        :returns: A :doc:`result`

        .. warning::
            You must be authenticated as the given user.

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('events.users.list_org_events',
                                    user=user, org=org)
        return self._get_normal_result(request)
