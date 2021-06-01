# -*- encoding: utf-8 -*-

from pygithub3.core.client import Client
from pygithub3.core.errors import NotFound
from pygithub3.core.result import smart, normal
from pygithub3.requests.base import Factory


class Service(object):
    """
    You can configure each service with this keyword variables:

    :param str login: Username to authenticate
    :param str password: Username to authenticate
    :param str user: Default username in requests
    :param str repo: Default repository in requests
    :param str token: Token to OAuth
    :param int per_page: Items in each page of multiple returns
    :param str base_url: To support another github-related API (untested)
    :param stream verbose: Stream to write debug logs
    :param timeout float: Timeout for requests

    You can configure the **authentication** with BasicAuthentication (login
    and password) and with `OAuth <http://developer.github.com/v3/oauth/>`_ (
    token).
    If you include ``login``, ``password`` and ``token`` in config; Oauth has
    precedence

    Some API requests need ``user`` and/or ``repo`` arguments (e.g
    :ref:`repos service <config precedence>`).
    You can configure the default value here to avoid repeating

    Some API requests return multiple resources with pagination. You can
    configure how many items has each page.

    You can configure ``verbose`` logging like `requests library <http://docs.
    python-requests.org/en/v0.10.6/user/advanced/#verbose-logging>`_
    """

    def __init__(self, **config):
        self._client = Client(**config)
        self.request_builder = Factory()

    @property
    def remaining_requests(self):
        return Client.remaining_requests

    def get_user(self):
        return self._client.user

    def set_user(self, user):
        """ Set user

        :param str user: Default username in requests
        """
        self._client.user = user

    def get_repo(self):
        return self._client.repo

    def set_repo(self, repo):
        """ Set repository

        :param str repo: Default repository in requests
        """
        self._client.repo = repo

    def set_credentials(self, login, password):
        """ Set Basic Authentication

        :param str login: Username to authenticate
        :param str password: Username to authenticate
        """
        self._client.set_credentials(login, password)

    def set_token(self, token):
        """ Set OAuth token

        :param str token: Token to OAuth
        """
        self._client.set_token(token)

    #TODO: Refact as decorator::
    """
        Reason: make_request and request_builder ... are confusing names
        @precedence('user')
        def list(self, sha, user=None):
    """
    def make_request(self, request, **kwargs):
        if 'user' in kwargs:
            kwargs['user'] = kwargs['user'] or self.get_user()
        if 'repo' in kwargs:
            kwargs['repo'] = kwargs['repo'] or self.get_repo()
        return self.request_builder(request, **kwargs)

    def _request(self, verb, request, **kwargs):
        self._client.request(verb, request, **kwargs)

    def _bool(self, request, **kwargs):
        try:
            self._client.head(request, **kwargs)
            return True
        except NotFound:
            return False

    def _patch(self, request, **kwargs):
        input_data = request.get_body()
        response = self._client.patch(request, data=input_data, **kwargs)
        return request.resource.loads(response.content)

    def _put(self, request, **kwargs):
        """ Bug in Github API? requests library?

        I must send data when the specifications' of some PUT request are 'Not
        send input data'. If I don't do that and send data as None, the
        requests library doesn't send 'Content-length' header and the server
        returns 411 - Required Content length (at least 0)

        For instance:
            - follow-user request doesn't send input data
            - merge-pull request send data

        For that reason I must do a conditional because I don't want to return
        an empty string on follow-user request because it could be confused

        Related: https://github.com/github/developer.github.com/pull/52
        """
        input_data = request.get_body() or 'PLACEHOLDER'
        response = self._client.put(request, data=input_data, **kwargs)
        if response.status_code != 204:  # != NO_CONTENT
            return request.resource.loads(response.content)

    def _delete(self, request, **kwargs):
        input_data = request.get_body()
        self._client.delete(request, data=input_data, **kwargs)

    def _post(self, request, **kwargs):
        input_data = request.get_body()
        response = self._client.post(request, data=input_data, **kwargs)
        return request.resource.loads(response.content)

    def _get(self, request, **kwargs):
        response = self._client.get(request, **kwargs)
        return request.resource.loads(response.content)

    def _get_result(self, request, **kwargs):
        method = smart.Method(self._client.get, request, **kwargs)
        return smart.Result(method)

    def _get_normal_result(self, request, **kwargs):
        method = normal.Method(self._client.get, request, **kwargs)
        return normal.Result(method)


# XXX: Refact to set_<type> method
class MimeTypeMixin(object):
    """
    Mimetype support to Services

    Adds 4 public functions to service:
    """

    VERSION = 'beta'

    def __set_mimetype(self, mimetype):
        self.mimetype = 'application/vnd.github.%s.%s+json' % (
            self.VERSION, mimetype)

    def set_raw(self):
        """ Resource will have ``body`` attribute """
        self.__set_mimetype('raw')

    def set_text(self):
        """ Resource will have ``body_text`` attribute """
        self.__set_mimetype('text')

    def set_html(self):
        """ Resource will have ``body_html`` attribute """
        self.__set_mimetype('html')

    def set_full(self):
        """ Resource will have ``body``, ``body_text`` and ``body_html``
        attributes """
        self.__set_mimetype('full')

    def _get_mimetype_as_header(self):
        try:
            return {'headers': {'Accept': self.mimetype}}
        except AttributeError:
            return {}
