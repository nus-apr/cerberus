# -*- encoding: utf-8 -*-

from pygithub3.services.base import Service, MimeTypeMixin
from .base import DummyRequest

base_url = 'https://api.github.com/'


def _(request):
    return "%s%s" % (base_url, request)


class DummyService(Service, MimeTypeMixin):

    def dummy_request(self):
        self._get(DummyRequest(), **self._get_mimetype_as_header())
