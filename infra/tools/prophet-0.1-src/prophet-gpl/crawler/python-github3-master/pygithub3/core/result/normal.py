#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from . import base
from .link import Link


class Method(base.Method):
    """ Cache support and builds next request """

    def __init__(self, *args, **kwargs):
        super(Method, self).__init__(*args, **kwargs)
        self.next = True

    def cached(func):
        def wrapper(self, page=1):
            if str(page) in self.cache:
                return self.cache[str(page)]['content']
            return func(self, page)
        return wrapper

    def next_getter_from(self, response):
        link = Link(response.headers.get('link'))
        if hasattr(link, 'next'):
            return base.functools.partial(self.method, **link.next.params)
        self.next = False

    @cached
    def __call__(self, page=1):
        prev = self.cache.get(str(page - 1))
        method = prev and prev['next'] or self.method
        response = method()
        self.cache[str(page)] = {
            'content': self.resource.loads(response.content),
            'next': self.next_getter_from(response)
        }
        return self.cache[str(page)]['content']


class Page(base.Page):
    """ Consumed when instance """

    def __init__(self, getter, page=1):
        super(Page, self).__init__(getter, page)
        content = getter(page)
        self.iterable = iter(content)
        self.count = len(content)


class Result(base.Result):
    """
    It's a middle-lazy iterator, because to get a new page it needs
    make a real request, besides it's **cached**, so never repeats a request.

    You have several ways to consume it

    #. Iterating over the result::

        result = some_request()
        for page in result:
            for resource in page:
                print resource

    #. With a generator::

        result = some_request()
        for resource in result.iterator():
            print resource

    #. As a list::

        result = some_request()
        print result.all()

    """

    """ TODO: limit in {all/iterator}
    .. note::
        You can use ``limit`` with `all` and `iterator`
        ::
            result = some_request()
            _5resources = result.all(limit=5)

        This exists because it can't request a explitic page, and some requests
        can have thousand of resources (e.g Repository's commits)
    """

    def __init__(self, method):
        super(Result, self).__init__(method)
        self._counter = 0
        self._cached = False

    def _get_cached(func):
        def wrapper(self):
            if self._cached:
                if str(self._counter) in self.getter.cache:
                    page = Page(self.getter, self._counter)
                    self._counter += 1
                    return page
                self._reset()
                raise StopIteration
            return func(self)
        return wrapper

    @_get_cached
    def __next__(self):
        if self.getter.next:
            self._counter += 1
            return Page(self.getter, self._counter)
        self._reset()
        raise StopIteration

    def _reset(self):
        self._counter = 1
        self._cached = True
