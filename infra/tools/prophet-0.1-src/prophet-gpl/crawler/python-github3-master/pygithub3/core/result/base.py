#!/usr/bin/env python
# -*- encoding: utf-8 -*-

import functools


class Method(object):
    """ It wraps the requester method, with behaviour to results """

    def __init__(self, method, request, **method_args):
        self.method = functools.partial(method, request, **method_args)
        self.resource = request.resource
        self.cache = {}

    def __call__(self):
        raise NotImplementedError


class Page(object):
    """ Iterator of resources """

    def __init__(self, getter, page=1):
        self.getter = getter
        self.page = page

    def __iter__(self):
        return self

    def __add__(self, number):
        return self.page + number

    def __radd__(self, number):
        return number + self.page

    def __sub__(self, number):
        return self.page - number

    def __rsub__(self, number):
        return number - self.page

    def __lt__(self, number):
        return self.page < number

    def __le__(self, number):
        return self.page <= number

    def __eq__(self, number):
        return self.page == number

    def __ne__(self, number):
        return self.page != number

    def __gt__(self, number):
        return self.page > number

    def __ge__(self, number):
        return self.page >= number

    @property
    def resources(self):
        return getattr(self, 'count', None) or '~'

    def get_content(func):
        def wrapper(self):
            if not hasattr(self, 'count'):
                content = self.getter(self.page)
                self.count = len(content)
                self.iterable = iter(content)
            return func(self)
        return wrapper

    @get_content
    def __next__(self):
        try:
            return self.iterable.next()
        except StopIteration:
            self.iterable = iter(self.getter(self.page))
            raise StopIteration

    def next(self):
        return self.__next__()

    def __str__(self):
        return '<{name}{page} resources={resources}>'.format(
                name=self.__class__.__name__,
                page=self.page,
                resources=self.resources)


class Result(object):
    """ Iterator of pages """

    def __init__(self, method):
        self.getter = method

    def __iter__(self):
        return self

    def next(self):
        return self.__next__()

    def iterator(self):
        """ generator """
        for page in self:
            for resource in page:
                yield resource

    def all(self):
        return list(self.iterator())
