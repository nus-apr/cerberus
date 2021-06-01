#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class Tags(Service):
    """Consume `Tags API <http://developer.github.com/v3/git/tags/>`_"""

    def get(self, sha, user=None, repo=None):
        """ Get a tag

        :param str sha: The sha of the tag to get.
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.tags.get', sha=sha, user=user,
            repo=repo)
        return self._get(request)

    def create(self, data, user=None, repo=None):
        """ Create a tag

        :param dict data: Input. See `github tags doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.tags.create', body=data,
            user=user, repo=repo)
        return self._post(request)
