#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Service


class Followers(Service):
    """ Consume `Followers API
    <http://developer.github.com/v3/users/followers/>`_
    """

    def list(self, user=None):
        """ Get user's followers

        :param str user: Username
        :returns: A :doc:`result`

        If you call it without user and you are authenticated, get the
        authenticated user's followers

        .. warning::
            If you aren't authenticated and call without user, it returns 403

        ::

            followers_service.list()
            followers_service.list('octocat')
        """
        request = self.request_builder('users.followers.list', user=user)
        return self._get_result(request)

    def list_following(self, user=None):
        """ Get who a user is following

        :param str user: Username
        :returns: A :doc:`result`

        If you call it without user and you are authenticated, get the
        authenticated user's followings

        .. warning::
            If you aren't authenticated and call without user, it returns 403

        ::

            followers_service.list_following()
            followers_service.list_following('octocat')
        """
        request = self.request_builder('users.followers.listfollowing',
            user=user)
        return self._get_result(request)

    def is_following(self, user):
        """ Check if you are following a user

        :param str user: Username
        """
        request = self.request_builder('users.followers.isfollowing',
            user=user)
        return self._bool(request)

    def follow(self, user):
        """ Follow a user

        :param str user: Username

        .. warning::
            You must be authenticated
        """
        request = self.request_builder('users.followers.follow', user=user)
        self._put(request)

    def unfollow(self, user):
        """ Unfollow a user

        :param str user: Username

        .. warning::
            You must be authenticated
        """
        request = self.request_builder('users.followers.unfollow', user=user)
        self._delete(request)
