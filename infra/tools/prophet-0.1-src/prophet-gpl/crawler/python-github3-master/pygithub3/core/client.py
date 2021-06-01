# -*- encoding: utf-8 -*-

import requests

from .errors import GithubError

VALID_REQUEST_ARGS = set((
    'params', 'data', 'headers', 'cookies', 'files', 'auth', 'timeout',
    'allow_redirects', 'proxies', 'return_response', 'config',
    'prefetch', 'verify'))


class Client(object):
    """ Client to send configurated requests"""

    remaining_requests = '~'

    def __init__(self, **kwargs):
        self.requester = requests.session()
        self.config = {
            'per_page': 100,
            'base_url': 'https://api.github.com/'
        }
        self.config.update(kwargs)
        self.set_credentials(self.config.get('login'),
                             self.config.get('password'))
        self.set_token(self.config.get('token'))
        self.__set_params(self.config)

    @property
    def user(self):
        return self.config.get('user')

    @user.setter
    def user(self, user):
        self.config['user'] = user

    @property
    def repo(self):
        return self.config.get('repo')

    @repo.setter
    def repo(self, repo):
        self.config['repo'] = repo

    def set_credentials(self, login, password):
        if login and password:
            self.requester.auth = (login, password)

    def set_token(self, token):
        if token:
            self.requester.params.append(('access_token', token))

    def __set_params(self, config):
        per_page = ('per_page', config.get('per_page'))
        self.requester.params.append(per_page)
        if config.get('verbose'):
            self.requester.config = {'verbose': config['verbose']}
        if config.get('timeout'):
            self.requester.timeout = config['timeout']

    def __parse_kwargs(func):
        """ Decorator to put extra args into requests.params """

        def wrapper(self, verb, request, **kwargs):
            diffs = set(kwargs.keys()) - VALID_REQUEST_ARGS
            new_params = kwargs.get('params', {})
            for key in diffs:  # Put each key in new_params and delete it
                new_params[key] = kwargs[key]
                del kwargs[key]
            kwargs['params'] = new_params
            return func(self, verb, request, **kwargs)
        return wrapper

    @__parse_kwargs
    def request(self, verb, request, **kwargs):
        request = "%s%s" % (self.config['base_url'], request)
        response = self.requester.request(verb, request, **kwargs)
        Client.remaining_requests = response.headers.get(
            'x-ratelimit-remaining', -1)
        GithubError(response).process()
        return response

    def get(self, request, **kwargs):
        response = self.request('get', request, **kwargs)
        assert response.status_code == 200
        return response

    def post(self, request, **kwargs):
        response = self.request('post', request, **kwargs)
        assert response.status_code == 201
        return response

    def patch(self, request, **kwargs):
        response = self.request('patch', request, **kwargs)
        assert response.status_code == 200
        return response

    def put(self, request, **kwargs):
        response = self.request('put', request, **kwargs)
        # assert response.status_code != '204'
        # I don't do an assert. See `services.base.Service._put` comment
        return response

    def delete(self, request, **kwargs):
        response = self.request('delete', request, **kwargs)
        assert response.status_code == 204
        return response

    def head(self, request, **kwargs):
        return self.request('head', request, **kwargs)
