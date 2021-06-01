#!/usr/bin/env python
# -*- encoding: utf-8 -*-

import requests

from . import Service


class Downloads(Service):
    """ Consume `Downloads API
    <http://developer.github.com/v3/repos/downloads>`_ """

    def list(self, user=None, repo=None):
        """ Get repository's downloads

        :param str user: Username
        :param str repo: Repository
        :returns: A :doc:`result`

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.downloads.list',
            user=user, repo=repo)
        return self._get_result(request)

    def get(self, id, user=None, repo=None):
        """ Get a single download

        :param int id: Download id
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.downloads.get',
            id=id, user=user, repo=repo)
        return self._get(request)

    def create(self, data, user=None, repo=None):
        """ Create a new download

        :param dict data: Input. See `github downloads doc`_
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`

        It is a two step process. After you create the download, you must
        call the ``upload`` function of ``Download`` resource with
        ``file_path``

        .. warning::
            In `alpha` state

        ::

            # Step 1
            download = downloads_service.create(
                dict(name='new_download', size=1130),
                user='octocat', repo='oct_repo')

            # Step 2
            download.upload('/home/user/file.ext')
        """
        request = self.make_request('repos.downloads.create',
            body=data, user=user, repo=repo)
        download = self._post(request)

        # TODO: improve it. e.g Manage all with file desc
        def upload(file_path):
            """ """
            data = download.ball_to_upload()
            files = {'File': open(file_path, 'rb')}
            return requests.post(download.s3_url, data=data, files=files)

        download.upload = upload
        return download

    def delete(self, id, user=None, repo=None):
        """ Delete a download

        :param int id: Download id
        :param str user: Username
        :param str repo: Repository

        .. note::
            Remember :ref:`config precedence`
        """
        request = self.make_request('repos.downloads.delete',
            id=id, user=user, repo=repo)
        self._delete(request)
