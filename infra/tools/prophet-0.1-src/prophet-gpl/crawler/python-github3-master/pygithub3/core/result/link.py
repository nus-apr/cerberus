#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from urlparse import urlparse, parse_qs

from pygithub3.core.third_libs.link_header import parse_link_value


class Link(str):

    class Url(str):

        @property
        def query(self):
            return urlparse(self).query

        @property
        def params(self):
            return dict([
                (param, values.pop())
                for param, values in parse_qs(self.query).items()])

    def __init__(self, object_):
        str.__init__(object_)
        parsed = parse_link_value(self)
        for url in parsed:
            setattr(self, parsed[url]['rel'], Link.Url(url))
