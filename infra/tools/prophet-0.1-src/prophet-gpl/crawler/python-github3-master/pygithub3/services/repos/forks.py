#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Service


class Forks(Service):
    """ Consume `Forks API
    <http://developer.github.com/v3/repos/forks>`_ """

    def list(self, user=None, repo=None, sort='newest'):
        """ Get repository's forks

        :param str user: Username
        :param str repo: Repository
        :param str sort: Order resources (optional). See `github forks doc`_
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`

        ::

            forks_service.list(user='octocat', repo='oct_repo', sort='oldest')
        """
        request = self.make_request('repos.forks.list', user=user, repo=repo)
        return self._get_result(request, sort=sort)

    def create(self, user=None, repo=None, org=None):
        """ Fork a repository

        :param str user: Username
        :param str repo: Repository
        :param str org: Organization name (optional)

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated

        If you call it with ``org``, the repository will be forked into this
        organization.
        ::

            forks_service.create(user='octocat', repo='oct_repo')
            forks_service.create(user='octocat', repo='oct_repo',
                org='myorganization')
        """
        request = self.make_request('repos.forks.create', user=user, repo=repo)
        org = org and {'org': org} or {}
        return self._post(request, **org)
