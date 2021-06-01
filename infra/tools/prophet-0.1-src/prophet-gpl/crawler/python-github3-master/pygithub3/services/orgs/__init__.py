# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service
from .members import Members
from .teams import Teams


class Org(Service):
    """ Consume `Orgs API <http://developer.github.com/v3/orgs>`_ """

    def __init__(self, **config):
        self.members = Members(**config)
        self.teams = Teams(**config)
        super(Org, self).__init__(**config)

    def list(self, user=None):
        """ Get user's orgs

        :param str user: Username
        :returns: A :doc:`result`

        If you call it without user and you are authenticated, get the
        authenticated user's orgs, public and private.

        If you call it with a user, get the user's public orgs.

        ::

            org_service.list('copitux')
            org_service.list()
        """
        request = self.request_builder('orgs.list', user=user)
        return self._get_result(request)

    def get(self, org):
        """ Get a single org

        :param str org: Org name
        """
        request = self.request_builder('orgs.get', org=org)
        return self._get(request)

    def update(self, org, data):
        """ Update a single org

        :param str org: Org name
        :param dict data: Input. See `github orgs doc`_

        .. warning ::
            You must be authenticated

        ::

            org_service.update(dict(company='ACME Development',
                                    location='Timbuctoo'))
        """
        request = self.request_builder('orgs.update', org=org, body=data)
        return self._patch(request)
