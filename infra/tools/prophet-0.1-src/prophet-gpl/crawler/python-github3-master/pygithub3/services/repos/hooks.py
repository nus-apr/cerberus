#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Service


class Hooks(Service):
    """ Consume `Hooks API
    <http://developer.github.com/v3/repos/hooks>`_

    .. warning::
        You must be authenticated and have repository's admin-permission
    """

    def list(self, user=None, repo=None):
        """ Get repository's hooks

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.hooks.list', user=user, repo=repo)
        return self._get_result(request)

    def get(self, hook_id, user=None, repo=None):
        """ Get a single hook

        :param int hook_id: Hook id
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.hooks.get',
            id=hook_id, user=user, repo=repo)
        return self._get(request)

    def create(self, data, user=None, repo=None):
        """ Create a hook

        :param dict data: Input. See `github hooks doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        ::

            data = {
                "name": "acunote",
                "active": True,
                "config": {
                    'token': 'AAA...',
                },
                "events": ['push', 'issues'],
            }
            hooks_service.create(data, user='octocat', repo='oct_repo')
        """
        request = self.make_request('repos.hooks.create',
            user=user, repo=repo, body=data)
        return self._post(request)

    def update(self, hook_id, data, user=None, repo=None):
        """ Update a single hook

        :param int hook_id: Hook id
        :param dict data: Input. See `github hooks doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        ::

            hooks_service.update(42, dict(active=False), user='octocat',
                repo='oct_repo')
        """
        request = self.make_request('repos.hooks.update',
            id=hook_id, user=user, repo=repo, body=data)
        return self._patch(request)

    def test(self, hook_id, user=None, repo=None):
        """ Test a hook

        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        This will trigger the hook with the latest push to the current
        repository.
        """
        request = self.make_request('repos.hooks.test',
            id=hook_id, user=user, repo=repo)
        self._request('post', request)

    def delete(self, hook_id, user=None, repo=None):
        """ Delete a single hook

        :param int hook_id: Hook id
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.hooks.delete',
            id=hook_id, user=user, repo=repo)
        self._delete(request)
