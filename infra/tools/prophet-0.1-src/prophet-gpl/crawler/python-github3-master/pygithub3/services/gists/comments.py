#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service, MimeTypeMixin


class Comments(Service, MimeTypeMixin):
    """ Consume `Comments API
    <http://developer.github.com/v3/gists/comments>`_

    .. note::
        This service support :ref:`mimetypes-section` configuration
    """

    def list(self, gist_id):
        """ Get gist's comments

        :param int gist_id: Gist id
        :returns: A :doc:`result`
        """
        request = self.request_builder('gists.comments.list', gist_id=gist_id)
        return self._get_result(request, **self._get_mimetype_as_header())

    def get(self, id):
        """ Get a single comment

        :param int id: Comment id
        """
        request = self.request_builder('gists.comments.get', id=id)
        return self._get(request, **self._get_mimetype_as_header())

    def create(self, gist_id, message):
        """ Create a comment

        :param int gist_id: Gist id
        :param str message: Comment's message

        .. warning::
            You must be authenticated

        ::

            comment_service.create(1, 'comment')
        """
        request = self.request_builder('gists.comments.create',
            gist_id=gist_id, body={'body': message})
        return self._post(request, **self._get_mimetype_as_header())

    def update(self, id, message):
        """ Update a comment

        :param int id: Comment id
        :param str message: Comment's message

        .. warning::
            You must be authenticated
        """
        request = self.request_builder('gists.comments.update', id=id,
            body={'body': message})
        return self._patch(request, **self._get_mimetype_as_header())

    def delete(self, id):
        """ Delete a comment

        :param int id: Comment id

        .. warning::
            You must be authenticated
        """
        request = self.request_builder('gists.comments.delete', id=id)
        self._delete(request)
