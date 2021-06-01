#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service
from comments import Comments


class Gist(Service):
    """ Consume `Gists API <http://developer.github.com/v3/gists>`_ """

    def __init__(self, **config):
        self.comments = Comments(**config)
        super(Gist, self).__init__(**config)

    def list(self, user=None):
        """ Get user's gists

        :param str user: Username
        :returns: A :doc:`result`

        If you call it without user and you are authenticated, get the
        authenticated user's gists. but if you aren't authenticated get the
        public gists

        ::

            gist_service.list('copitux')
            gist_service.list()
        """
        request = self.request_builder('gists.list', user=user)
        return self._get_result(request)

    def public(self):
        """ Get public gists

        :returns: A :doc:`result`

        .. note ::
            Be careful iterating the result
        """
        request = self.request_builder('gists.public')
        return self._get_result(request)

    def starred(self):
        """ Get authenticated user's starred gists

        :returns: A :doc:`result`

        .. warning::
            You must be authenticated
        """
        request = self.request_builder('gists.starred')
        return self._get_result(request)

    def get(self, id):
        """ Get a single gist

        :param int id: Gist id
        """
        request = self.request_builder('gists.get', id=id)
        return self._get(request)

    def create(self, data):
        """ Create a gist

        :param dict data: Input. See `github gists doc`_

        ::

            gist_service.create(dict(description='some gist', public=True,
                files={'xample.py': {'content': 'import code'}}))
        """
        request = self.request_builder('gists.create', body=data)
        return self._post(request)

    def update(self, id, data):
        """ Update a single gist

        :param int id: Gist id
        :param dict data: Input. See `github gists doc`_

        .. warning ::
            You must be authenticated

        ::

            gist_service.update(dict(description='edited',
                files={'xample.py': {
                    'filename': 'new_xample.py',
                    'content': 'import new_code'}}))
        """
        request = self.request_builder('gists.update', id=id, body=data)
        return self._patch(request)

    def star(self, id):
        """ Star a gist

        :param int id: Gist id

        .. warning ::
            You must be authenticated

        """
        request = self.request_builder('gists.star', id=id)
        self._put(request)

    def unstar(self, id):
        """ Unstar a gist

        :param int id: Gist id

        .. warning ::
            You must be authenticated

        """
        request = self.request_builder('gists.unstar', id=id)
        return self._delete(request)

    def is_starred(self, id):
        """ Check if a gist is starred

        :param int id: Gist id

        .. warning ::
            You must be authenticated

        """
        request = self.request_builder('gists.is_starred', id=id)
        return self._bool(request)

    def fork(self, id):
        """ Fork a gist

        :param int id: Gist id

        .. warning ::
            You must be authenticated

        """

        request = self.request_builder('gists.fork', id=id)
        return self._post(request)

    def delete(self, id):
        """ Delete a gist

        :param int id: Gist id

        .. warning ::
            You must be authenticated

        """
        request = self.request_builder('gists.delete', id=id)
        return self._delete(request)
