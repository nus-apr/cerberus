# -*- encoding: utf-8 -*-

from mock import Mock

from pygithub3.core.client import Client
from pygithub3.core.result import smart, normal, base
from pygithub3.tests.utils.core import (TestCase, mock_paginate_github_in_GET,
    request, mock_no_paginate_github_in_GET, MockPaginate)


class ResultInitMixin(object):

    def setUp(self):
        self.c = Client()
        self.get_request = Mock(side_effect=self.mock)
        self.resource_loads = request.resource.loads
        self.c.get = self.get_request
        self.r = smart.Result(smart.Method(self.c.get, request))

    def tearDown(self):
        self.resource_loads.reset_mock()  # It mocks class method


class TestSmartResultWithPaginate(ResultInitMixin, TestCase):

    @property
    def mock(self):
        return mock_paginate_github_in_GET

    def test_iteration_CALLS(self):
        self.assertEqual(self.get_request.call_count, 0)
        self.assertEqual(self.resource_loads.call_count, 0)
        list(self.r)
        self.get_request.assert_called_once_with(request, page=1)
        self.assertEqual(self.resource_loads.call_count, 1)

    def test_consumed_are_Pages(self):
        pages_that_are_Pages = len(
            filter(lambda page: isinstance(page, base.Page), list(self.r)))
        self.assertEqual(pages_that_are_Pages, 3, 'There are not 3 Pages objs')

    def test_all_iteration_CALLS(self):
        self.r.all()
        self.assertEqual(self.get_request.call_count, 3)
        self.assertEqual(self.resource_loads.call_count, 3)

    def test_CACHE_with_renew_iterations(self):
        self.r.all()
        self.r.all()
        self.assertEqual(self.get_request.call_count, 3)
        self.assertEqual(len(self.r.getter.cache), 3)
        self.assertEqual(self.resource_loads.call_count, 3)

    def test_ITERATOR_calls(self):
        self.r.iterator()
        self.assertEqual(self.get_request.call_count, 0)
        self.assertEqual(self.resource_loads.call_count, 0)


class TestSmartResultWithoutPaginate(ResultInitMixin, TestCase):

    @property
    def mock(self):
        return mock_no_paginate_github_in_GET

    def test_iteration_stop_at_1(self):
        self.r.next()
        self.assertRaises(StopIteration, self.r.next)

    def test_get_only_1page(self):
        self.r.all()
        self.assertEqual(self.get_request.call_count, 1)
        self.assertEqual(self.resource_loads.call_count, 1)


class TestNormalResult(TestSmartResultWithPaginate, TestCase):

    @property
    def mock(self):
        return MockPaginate()

    def setUp(self):
        super(TestNormalResult, self).setUp()
        self.r = normal.Result(normal.Method(self.c.get, request))

    def test_iteration_CALLS(self):
        self.assertEqual(self.get_request.call_count, 0)
        self.assertEqual(self.resource_loads.call_count, 0)
        list(self.r)
        self.assertEqual(self.get_request.call_count, 3)
        self.assertEqual(self.resource_loads.call_count, 3)

    """ Inherit tests. They share behaviour
        def test_consumed_are_Pages(self):
        def test_all_iteration_CALLS(self):
        def test_CACHE_with_renew_iterations(self):
        def test_ITERATOR_calls(self):
    """
