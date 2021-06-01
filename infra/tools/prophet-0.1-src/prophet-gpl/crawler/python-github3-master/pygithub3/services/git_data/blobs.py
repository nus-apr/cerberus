#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service, MimeTypeMixin


class Blobs(Service, MimeTypeMixin):
    """Consume `Blobs API <http://developer.github.com/v3/git/blobs/>`_"""

    def get(self, sha, user=None, repo=None):
        """Get a particular blob

        :param str sha: The sha of the blob to get
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.blobs.get', sha=sha,
            user=user, repo=repo)
        return self._get(request, **self._get_mimetype_as_header())

    def create(self, data, user=None, repo=None):
        """Create a blob

        :param dict data: Data describing the blob to create
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.blobs.create', body=data,
            user=user, repo=repo)
        return self._post(request)
