# -*- coding: utf-8 -*-

from datetime import datetime

from pygithub3.tests.utils.core import TestCase
from pygithub3.core import json


class TestJson(TestCase):
    """
    Test dates parse and normalize
    """

    dict_ = {
        'date_ok': datetime(2008, 1, 14, 4, 33, 35),
        'date_fake': 'some_fake',
        'list': [1, 2, 3],
        'nested_dict': {'with_date': datetime(2008, 1, 14, 4, 33, 35)},
    }
    json_ = '{"date_fake": "some_fake", "list": [1, 2, 3], "date_ok": "2008-01-14T04:33:35Z", "nested_dict": {"with_date": "2008-01-14T04:33:35Z"}}'

    def test_encoder(self):
        to_json = json.dumps(self.dict_)
        self.assertEquals(to_json, self.json_)

    def test_decoder(self):
        to_dict = json.loads(self.json_)
        self.assertEquals(self.dict_, to_dict)
