#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service, MimeTypeMixin
from .collaborators import Collaborators
from .commits import Commits
from .downloads import Downloads
from .forks import Forks
from .keys import Keys
from .watchers import Watchers
from .hooks import Hooks


class Repo(Service):
    """ Consume `Repos API <http://developer.github.com/v3/repos>`_ """

    def __init__(self, **config):
        self.collaborators = Collaborators(**config)
        self.commits = Commits(**config)
        self.downloads = Downloads(**config)
        self.forks = Forks(**config)
        self.keys = Keys(**config)
        self.watchers = Watchers(**config)
        self.hooks = Hooks(**config)
        super(Repo, self).__init__(**config)

    def list(self, user=None, type='all'):
        """ Get user's repositories

        :param str user: Username
        :param str type: Filter by type (optional). See `github repos doc`_
        :returns: A :doc:`result`

        If you call it without user and you are authenticated, get the
        authenticated user's repositories

        .. warning::
            If you aren't authenticated and call without user, it returns 403

        ::

            repo_service.list('copitux', type='owner')
            repo_service.list(type='private')
        """
        request = self.request_builder('repos.list', user=user)
        return self._get_result(request, type=type)

    def list_by_org(self, org, type='all'):
        """ Get organization's repositories

        :param str org: Organization name
        :param str type: Filter by type (optional). See `github repos doc`_
        :returns: A :doc:`result`

        ::

            repo_service.list_by_org('myorganization', type='member')
        """
        request = self.make_request('repos.list_by_org', org=org)
        return self._get_result(request, type=type)

    def create(self, data, in_org=None):
        """ Create a new repository

        :param dict data: Input. See `github repos doc`_
        :param str in_org: Organization where create the repository (optional)

        .. warning::

            You must be authenticated

            If you use ``in_org`` arg, the authenticated user must be a member
            of <in_org>

        ::

            repo_service.create(dict(name='new_repo', description='desc'))
            repo_service.create(dict(name='new_repo_in_org', team_id=2300),
                in_org='myorganization')
        """
        request = self.make_request('repos.create', org=in_org, body=data)
        return self._post(request)

    def delete(self, user=None, repo=None):
        """ Delete a single repo

        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.delete', user=user, repo=repo)
        return self._delete(request)

    def get(self, user=None, repo=None):
        """ Get a single repo

        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.get', user=user, repo=repo)
        return self._get(request)

    def update(self, data, user=None, repo=None):
        """ Update a single repository

        :param dict data: Input. See `github repos doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        .. warning::
            You must be authenticated

        ::

            repo_service.update(dict(has_issues=True), user='octocat',
                repo='oct_repo')
        """
        request = self.make_request('repos.update', body=data,
            user=user, repo=repo)
        return self._patch(request)

    def __list_contributors(self, user=None, repo=None, **kwargs):
        request = self.make_request('repos.list_contributors',
            user=user, repo=repo)
        return self._get_result(request, **kwargs)

    def list_contributors(self, user=None, repo=None):
        """ Get repository's contributors

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        return self.__list_contributors(user, repo)

    def list_contributors_with_anonymous(self, user=None, repo=None):
        """ Like :attr:`~pygithub3.services.repos.Repo.list_contributors` plus
        anonymous """
        return self.__list_contributors(user, repo, anom=True)

    def list_languages(self, user=None, repo=None):
        """ Get repository's languages

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.list_languages',
            user=user, repo=repo)
        return self._get(request)

    def list_teams(self, user=None, repo=None):
        """ Get repository's teams

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.list_teams', user=user, repo=repo)
        return self._get_result(request)

    def list_tags(self, user=None, repo=None):
        """ Get repository's tags

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.list_tags', user=user, repo=repo)
        return self._get_result(request)

    def list_branches(self, user=None, repo=None):
        """ Get repository's branches

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.list_branches',
            user=user, repo=repo)
        return self._get_result(request)
