# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class Members(Service):
    """ Consume `Members API <http://developer.github.com/v3/orgs/members/>`_
    """

    def list(self, org):
        """ Get org's members

        :param str org: Organisation name
        :returns: A :doc:`result`

        If you call it authenticated, and are a member of the org, public and
        private members will be visible.

        If not, only public members will be visible.
        """
        request = self.request_builder('orgs.members.list', org=org)
        return self._get_result(request)

    def is_member(self, org, user):
        """ Determine if user is a member of org

        :param str org: Organisation name
        :param str user: User name
        """
        request = self.request_builder('orgs.members.is_member', org=org,
            user=user)
        return self._bool(request)

    def remove_member(self, org, user):
        """ Remove user from all teams in org

        :param str org: Organisation name
        :param str user: User name

        .. warning ::
            You must be authenticated and an owner of org

        """
        request = self.request_builder('orgs.members.delete', org=org,
            user=user)
        return self._delete(request)

    def list_public(self, org):
        """ Get org's public members

        :param str org: Organisation name
        :returns: A :doc:`result`
        """
        request = self.request_builder('orgs.members.listpublic', org=org)
        return self._get_result(request)

    def is_public_member(self, org, user):
        """ Determine if user is a public member of org

        :param str org: Organisation name
        :param str user: User name
        """
        request = self.request_builder('orgs.members.is_public_member',
                                       org=org, user=user)
        return self._bool(request)

    def publicize_membership(self, org, user):
        """ Publicize user's membership in org

        :param str org: Organisation name
        :param str user: User name

        .. warning ::
            You must be authenticated and the user, or an owner of the org

        """
        request = self.request_builder('orgs.members.publicize',
                                       org=org, user=user)
        return self._put(request)

    def conceal_membership(self, org, user):
        """ Conceal user's membership in org

        :param str org: Organisation name
        :param str user: User name

        .. warning ::
            You must be authenticated and the user, or an owner of the org

        """
        request = self.request_builder('orgs.members.conceal',
                                       org=org, user=user)
        return self._delete(request)
