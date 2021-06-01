#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service


class Labels(Service):
    """ Consume `Labels API
    <http://developer.github.com/v3/issues/labels>`_ """

    def list(self, user=None, repo=None):
        """ Get repository's labels

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.list', user=user, repo=repo)
        return self._get_result(request)

    def get(self, name, user=None, repo=None):
        """ Get a single label

        :param str name: Label name
        :param str user: Username
        :param str repo: Repo name

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.get', user=user,
            repo=repo, name=name)
        return self._get(request)

    def create(self, data, user=None, repo=None):
        """ Create a label on an repo

        :param dict data: Input. See `github labels doc`_
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.create', user=user,
            repo=repo, body=data)
        return self._post(request)

    def update(self, name, data, user=None, repo=None):
        """ Update a label on an repo

        :param str name: Label name
        :param dict data: Input. See `github labels doc`_
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.update', user=user,
            repo=repo, name=name, body=data)
        return self._patch(request)

    def delete(self, name, user=None, repo=None):
        """ Delete a label on an repo

        :param str name: Label name
        :param str user: Username
        :param str repo: Repo name

        .. warning::
            You must be authenticated

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.delete', user=user,
            repo=repo, name=name)
        return self._delete(request)

    def list_by_issue(self, number, user=None, repo=None):
        """ List labels for an issue

        :param int number: Issue number
        :param str user: Username
        :param str repo: Repo name
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.list_by_issue', user=user,
            repo=repo, number=number)
        return self._get(request)

    def add_to_issue(self, number, labels, user=None, repo=None):
        """ Add labels to issue

        :param int number: Issue number
        :param str user: Username
        :param str repo: Repo name
        :param list labels: Label names
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`

        ::

            labels_service.add_to_issue(2, user='github', repo='github',
                'label1', 'label2', 'label3')
        """
        request = self.make_request('issues.labels.add_to_issue', user=user,
            repo=repo, number=number, body=map(str, labels))
        return self._post(request)

    def remove_from_issue(self, number, label, user=None, repo=None):
        """ Remove a label from an issue

        :param int number: Issue number
        :param str label: Label name
        :param str user: Username
        :param str repo: Repo name
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.remove_from_issue',
                                       user=user,
                                       repo=repo,
                                       number=number,
                                       name=label)
        return self._delete(request)

    def replace_all(self, number, labels, user=None, repo=None):
        """ Replace all labels for a issue

        :param int number: Issue number
        :param list labels: New labels
        :param str user: Username
        :param str repo: Repo name
        :returns: A :doc:`result`

        .. note::
            If labels weren't especified, it'd remove all labels from the issue

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.replace_all',
                                       user=user,
                                       repo=repo,
                                       number=number,
                                       body=map(str, labels))
        return self._put(request)

    def remove_all(self, number, user=None, repo=None):
        """ Remove all labels from a issue

        :param int number: Issue number
        :param str user: Username
        :param str repo: Repo name
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.remove_all',
                                       user=user,
                                       repo=repo,
                                       number=number,)
        return self._delete(request)

    def list_by_milestone(self, number, user=None, repo=None):
        """ Get labels for every issue in a milestone

        :param int number: Milestone ID
        :param str user: Username
        :param str repo: Repo name
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('issues.labels.list_by_milestone',
            user=user, repo=repo, number=number)
        return self._get_result(request)
