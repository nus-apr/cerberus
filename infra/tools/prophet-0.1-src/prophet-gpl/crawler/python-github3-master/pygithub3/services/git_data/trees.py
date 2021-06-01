#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class Trees(Service):
    """Consume `Trees API <http://developer.github.com/v3/git/trees/>`_"""

    def get(self, sha, recursive=False, user=None, repo=None):
        """ Get a tree object

        :param str sha: The SHA of the tree you want.
        :param bool recursive: Whether to resolve each sub-tree belonging to
                               this tree
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.trees.get', sha=sha, user=user,
            repo=repo)
        return self._get(request, recursive=recursive)

    def create(self, data, user=None, repo=None):
        """ Create a tree object

        :param dict data: Input. See `github trees doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.trees.create', body=data,
            user=user, repo=repo)
        return self._post(request)
