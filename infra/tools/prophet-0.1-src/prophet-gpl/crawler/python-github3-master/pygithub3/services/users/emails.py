#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Service


class Emails(Service):
    """ Consume `Emails API <http://developer.github.com/v3/users/emails/>`_

    .. warning::
        You must be authenticated for all requests
    """

    def list(self):
        """ Get user's emails

        :returns: A :doc:`result`
        """
        request = self.make_request('users.emails.list')
        return self._get_result(request)

    def add(self, *emails):
        """ Add emails

        :param list emails: Emails to add

        .. note::
            It rejects non-valid emails

        ::

            email_service.add('test1@xample.com', 'test2@xample.com')
        """
        request = self.make_request('users.emails.add', body=emails)
        return self._post(request)

    def delete(self, *emails):
        """ Delete emails

        :param list emails: List of emails

        ::

            email_service.delete('test1@xample.com', 'test2@xample.com')
        """
        request = self.make_request('users.emails.delete', body=emails)
        self._delete(request)
