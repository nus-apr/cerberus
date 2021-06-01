#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service
from .keys import Keys
from .emails import Emails
from .followers import Followers


class User(Service):
    """ Consume `Users API <http://developer.github.com/v3/users>`_ """

    def __init__(self, **config):
        self.keys = Keys(**config)
        self.emails = Emails(**config)
        self.followers = Followers(**config)
        super(User, self).__init__(**config)

    def get(self, user=None):
        """ Get a single user

        :param str user: Username

        If you call it without user and you are authenticated, get the
        authenticated user.

        .. warning::
            If you aren't authenticated and call without user, it returns 403

        ::

            user_service.get('copitux')
            user_service.get()
        """
        request = self.request_builder('users.get', user=user)
        return self._get(request)

    def update(self, data):
        """ Update the authenticated user

        :param dict data: Input to update

        ::

            user_service.update(dict(name='new_name', bio='new_bio'))
        """
        request = self.make_request('users.update', body=data)
        return self._patch(request)
