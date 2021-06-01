#!/usr/bin/env python
# -*- encoding: utf-8 -*-

try:
    from unittest2 import TestCase  # Python 2.6
except ImportError:
    from unittest import TestCase  # Python >2.7

from .base import Mock, DummyRequest

request = DummyRequest()
# Working without json but name it json-related to not confuse
json_content = [dict(name='dummy')]


# To smart results

def mock_paginate_github_in_GET(request, page):
    def header(page):
        return {'link': '<https://d.com/d?page=%s>; rel="last"' % page}

    def content(page):
        if page >= 3:
            return json_content
        return json_content * 2

    response = Mock()
    response.headers = header(3)
    response.content = content(page)
    return response


def mock_no_paginate_github_in_GET(request, page):
    response = Mock()
    response.headers = {}
    response.content = [json_content * 3]
    return response


# To normal results
class MockPaginate(object):

    def __init__(self):
        self.counter = 1

    def content(self):
        if self.counter >= 3:
            return json_content
        return json_content * 2

    def header(self):
        if self.counter >= 3:
            return {}
        return {'link': '<https://d.com/d?page=%s>; rel="next"' % self.counter}

    def __call__(self, *args, **kwargs):
        response = Mock()
        response.headers = self.header()
        response.content = self.content()
        self.counter += 1
        return response
