#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Service


class Watchers(Service):
    """ Consume `Watching API
    <http://developer.github.com/v3/repos/watching>`_ """

    def list(self, user=None, repo=None):
        """ Get repository's watchers

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.watchers.list',
            user=user, repo=repo)
        return self._get_result(request)

    def list_repos(self, user=None):
        """ Get repositories being watched by a user

        :param str user: Username
        :returns: A :doc:`result`

        If you call it without user and you are authenticated, get the
        repositories being watched by the authenticated user.

        .. warning::
            If you aren't authenticated and call without user, it returns 403

        ::

            watchers_service.list_repos('copitux')
            watchers_service.list_repos()
        """
        request = self.request_builder('repos.watchers.list_repos', user=user)
        return self._get_result(request)

    def is_watching(self, user=None, repo=None):
        """ Check if authenticated user is watching a repository

        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated
        """
        request = self.make_request('repos.watchers.is_watching',
            user=user, repo=repo)
        return self._bool(request)

    def watch(self, user=None, repo=None):
        """ Watch a repository

        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated
        """
        request = self.make_request('repos.watchers.watch',
            user=user, repo=repo)
        self._put(request)

    def unwatch(self, user=None, repo=None):
        """ Stop watching a repository

        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated
        """
        request = self.make_request('repos.watchers.unwatch',
            user=user, repo=repo)
        self._delete(request)
