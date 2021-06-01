# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service, MimeTypeMixin


class Comments(Service, MimeTypeMixin):
    """ Consume `Comments API
    <http://developer.github.com/v3/issues/comments>`_ """

    def list(self, number, user=None, repo=None):
        """ List comments for an issue

        :param int number: Issue number
        :param str user: Username
        :param str repo: Repo name
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.comments.list', user=user,
            repo=repo, number=number)
        return self._get_result(request)

    def get(self, id, user=None, repo=None):
        """ Get a single comment

        :param int id: Comment id
        :param str user: Username
        :param str repo: Repo name

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.comments.get', user=user,
            repo=repo, id=id)
        return self._get(request)

    def create(self, number, message, user=None, repo=None):
        """ Create a comment on an issue

        :param int number: Issue number
        :param str message: Comment message
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.comments.create', user=user,
            repo=repo, number=number, body={'body': message})
        return self._post(request)

    def update(self, id, message, user=None, repo=None):
        """ Update a comment on an issue

        :param int id: Issue id
        :param str message: Comment message
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.comments.edit', user=user,
            repo=repo, id=id, body={'body': message})
        return self._patch(request)

    def delete(self, id, user=None, repo=None):
        """ Delete a single comment

        :param int id: Comment id
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.comments.delete', user=user,
            repo=repo, id=id)
        self._delete(request)
