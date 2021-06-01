#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import Service


class Collaborators(Service):
    """ Consume `Repo Collaborators API
    <http://developer.github.com/v3/repos/collaborators>`_ """

    def list(self, user=None, repo=None):
        """ Get repository's collaborators

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.collaborators.list',
            user=user, repo=repo)
        return self._get_result(request)

    def add(self, collaborator, user=None, repo=None):
        """ Add collaborator to a repository

        :param str collaborator: Collaborator's username
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated and have perms in repository
        """
        request = self.make_request('repos.collaborators.add',
            collaborator=collaborator, user=user, repo=repo)
        return self._put(request)

    def is_collaborator(self, collaborator, user=None, repo=None):
        """ Check if a user is collaborator on repository

        :param str collaborator: Collaborator's username
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.collaborators.is_collaborator',
            collaborator=collaborator, user=user, repo=repo)
        return self._bool(request)

    def delete(self, collaborator, user=None, repo=None):
        """ Remove collaborator from repository

        :param str collaborator: Collaborator's username
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated and have perms in repository
        """
        request = self.make_request('repos.collaborators.delete',
            collaborator=collaborator, user=user, repo=repo)
        self._delete(request)
