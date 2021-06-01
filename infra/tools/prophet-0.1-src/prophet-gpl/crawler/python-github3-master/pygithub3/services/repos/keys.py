#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Service


class Keys(Service):
    """ Consume `Deploy keys API
    <http://developer.github.com/v3/repos/keys>`_ """

    def list(self, user=None, repo=None):
        """ Get repository's keys

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.keys.list', user=user, repo=repo)
        return self._get_result(request)

    def get(self, id, user=None, repo=None):
        """ Get a single repository key

        :param int id: Repository key id
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.keys.get',
            id=id, user=user, repo=repo)
        return self._get(request)

    def create(self, data, user=None, repo=None):
        """ Create a repository key

        :param dict data: Input. See `github keys doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated and have perms in the repository

        ::

            keys_service.create(dict(title='new key', key='ssh-rsa AAA...'),
                user='octocat', repo='oct_repo')
        """
        request = self.make_request('repos.keys.create',
            body=data, user=user, repo=repo)
        return self._post(request)

    def update(self, id, data, user=None, repo=None):
        """ Update a repository key

        :param int id: Repository key id
        :param dict data: Input. See `github keys doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated and have perms in the repository

        ::

            keys_service.update(42, dict(title='new title'),
                user='octocat', repo='oct_repo')
        """
        request = self.make_request('repos.keys.update',
            id=id, body=data, user=user, repo=repo)
        return self._patch(request)

    def delete(self, id, user=None, repo=None):
        """ Delete a repository key

        :param int id: Repository key id
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.keys.delete',
            id=id, user=user, repo=repo)
        self._delete(request)
