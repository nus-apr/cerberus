#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Service


class Keys(Service):
    """ Consume `Keys API <http://developer.github.com/v3/users/keys/>`_

    .. warning::
        You must be authenticated for all requests
    """

    def list(self):
        """ Get public keys

        :returns: A :doc:`result`
        """
        request = self.make_request('users.keys.list')
        return self._get_result(request)

    def get(self, key_id):
        """ Get a public key

        :param int key_id: Key id
        """
        request = self.make_request('users.keys.get',
            key_id=key_id)
        return self._get(request)

    def add(self, data):
        """ Add a public key

        :param dict data: Key (title and key attributes required)

        ::

            key_service.add(dict(title='host', key='ssh-rsa AAA...'))
        """
        request = self.make_request('users.keys.add',
            body=data)
        return self._post(request)

    def update(self, key_id, data):
        """ Update a public key

        :param int key_id: Key id
        :param dict data: Key (title and key attributes required)

        ::

            key_service.update(42, dict(title='host', key='ssh-rsa AAA...'))
        """
        request = self.make_request('users.keys.update',
            key_id=key_id, body=data)
        return self._patch(request)

    def delete(self, key_id):
        """ Delete a public key

        :param int key_id: Key id
        """
        request = self.make_request('users.keys.delete',
            key_id=key_id)
        self._delete(request)
