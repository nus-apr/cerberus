# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service, MimeTypeMixin
from .comments import Comments
from .events import Events
from .labels import Labels
from .milestones import Milestones


class Issue(Service, MimeTypeMixin):
    """ Consume `Issues API <http://developer.github.com/v3/issues>`_ """

    def __init__(self, **config):
        self.comments = Comments(**config)
        self.events = Events(**config)
        self.labels = Labels(**config)
        self.milestones = Milestones(**config)
        super(Issue, self).__init__(**config)

    def list(self, filter='assigned', state='open', labels='', sort='created',
            direction='desc', since=None):
        """ List your issues

        :param str filter: 'assigned', 'created', 'mentioned' or 'subscribed'
        :param str state: 'open' or 'closed'
        :param str labels: List of comma separated Label names. e.g: bug,ui,
                           @high
        :param str sort: 'created', 'updated' or 'comments'
        :param str direction: 'asc' or 'desc'
        :param datetime since: Date filter (datetime or str in ISO 8601)
        :returns: A :doc:`result`

        .. warning::
            You must be authenticated
        """
        params = dict(filter=filter, state=state, labels=labels, sort=sort,
            direction=direction)
        request = self.request_builder('issues.list')
        return self._get_result(request, **params)

    def list_by_repo(self, user=None, repo=None, milestone='*', state='open',
            assignee='*', mentioned='', labels='', sort='created',
            direction='desc', since=None):
        """ List issues for a repo

        :param str milestone: Milestone ID, 'none' or '*'
        :param str state: 'open' or 'closed'
        :param str assignee: Username, 'none' or '*'
        :param str mentioned: Username
        :param str labels: List of comma separated Label names. e.g: bug,ui,
                           @high
        :param str sort: 'created', 'updated' or 'comments'
        :param str direction: 'asc' or 'desc'
        :param datetime since: Date filter (datetime or str in ISO 8601)
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        params = dict(milestone=milestone, state=state, assignee=assignee,
            mentioned=mentioned, labels=labels, sort=sort, direction=direction)
        request = self.make_request('issues.list_by_repo', user=user,
            repo=repo)
        return self._get_result(request, **params)

    def get(self, number, user=None, repo=None):
        """ Get a single issue

        :param int number: Issue number
        :param str user: Username
        :param str repo: Repo name

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.get', user=user, repo=repo,
            number=number)
        return self._get(request)

    def create(self, data, user=None, repo=None):
        """ Create an issue

        :param dict data: Input. See `github issues doc`_
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`

        ::

            issues_service.create(dict(title='My test issue',
                body='This needs to be fixed ASAP.',
                assignee='copitux'))
        """
        request = self.make_request('issues.create', user=user, repo=repo,
            body=data)
        return self._post(request)

    def update(self, number, data, user=None, repo=None):
        """ Update an issue

        :param int number: Issue number
        :param dict data: Input. See `github issues doc`_
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.update', user=user, repo=repo,
            number=number, body=data)
        return self._patch(request)
