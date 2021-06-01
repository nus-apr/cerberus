#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class Milestones(Service):
    """ Consume `Milestones API
    <http://developer.github.com/v3/issues/milestones>`_ """

    def list(self, user=None, repo=None, state='open', sort='due_date',
            direction='desc'):
        """ List milestones for a repo

        :param str user: Username
        :param str repo: Repo name
        :param str state: 'open' or 'closed'
        :param str sort: 'due_date' or 'completeness'
        :param str direction: 'asc' or 'desc'
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.milestones.list', user=user,
            repo=repo)
        return self._get_result(request, state=state, sort=sort,
            direction=direction)

    def get(self, number, user=None, repo=None):
        """ Get a single milestone

        :param int number: Milestone number
        :param str user: Username
        :param str repo: Repo name

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.milestones.get', user=user,
            repo=repo, number=number)
        return self._get(request)

    def create(self, data, user=None, repo=None):
        """ Create a milestone

        :param dict data: Input. See `github milestones doc`_
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.milestones.create', user=user,
            repo=repo, body=data)
        return self._post(request)

    def update(self, number, data, user=None, repo=None):
        """ Update a milestone

        :param int number: Milestone number
        :param dict data: Input. See `github milestones doc`_
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.milestones.update', user=user,
            repo=repo, number=number, body=data)
        return self._patch(request)

    def delete(self, number, user=None, repo=None):
        """ Delete a milestone

        :param int number: Milestone number
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.milestones.delete', user=user,
            repo=repo, number=number)
        self._delete(request)
