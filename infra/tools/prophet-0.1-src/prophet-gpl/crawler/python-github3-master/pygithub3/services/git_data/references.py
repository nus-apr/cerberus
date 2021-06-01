#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class References(Service):
    """Consume `References API <http://developer.github.com/v3/git/refs/>`_"""

    def get(self, ref, user=None, repo=None):
        """ Get a reference

        :param str ref: The name of the reference to get
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. note::
            Remember that branch references look like "heads/<branch_name>"
        """
        request = self.make_request('git_data.references.get', ref=ref,
            user=user, repo=repo)
        return self._get(request)

    def list(self, namespace='', user=None, repo=None):
        """ List all the references

        :param str namespace: Limit the request to a particular type of
                              reference. For example, ``heads`` or ``tags``.
        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.references.list', user=user,
            repo=repo, namespace=namespace)
        return self._get_result(request)

    def create(self, data, user=None, repo=None):
        """ Create a reference

        :param dict data: Input. See `github refs doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.references.create', body=data,
            user=user, repo=repo)
        return self._post(request)

    def update(self, ref, data, user=None, repo=None):
        """ Update an existing reference

        :param str ref: The SHA of the reference to update
        :param dict data: Input. See `github refs doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.references.update', ref=ref,
            body=data, user=user, repo=repo)
        return self._patch(request)

    def delete(self, ref, user=None, repo=None):
        """Delete a reference

        :param str ref: The SHA of the reference to delete
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('git_data.references.delete', ref=ref,
            user=user, repo=repo)
        return self._delete(request)
