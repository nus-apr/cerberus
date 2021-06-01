# -*- encoding: utf-8 -*-

from datetime import datetime

from pygithub3.core import json
from pygithub3.resources.base import Raw
from pygithub3.tests.utils.core import TestCase
from pygithub3.tests.utils.resources import Nested, Simple, HasSimple

simple_resource = dict(type='simple')
has_simple = dict(type='has_simple', simple=simple_resource)
github_dict = dict(
    id=1,
    name='name_test',
    date='2008-01-14T04:33:35Z',
    simple=simple_resource,
    list_collection=[has_simple] * 2,
    items_collections=dict(arg1=has_simple, arg2=has_simple)
)
github_dict_nested = github_dict.copy()
github_dict.update({'self_nested': github_dict_nested})
github_dict.update({'self_nested_list': [github_dict_nested] * 2})
github_dict.update({'self_nested_dict': dict(arg1=github_dict_nested)})
github_return = json.dumps(github_dict)


class TestResourceMapping(TestCase):

    def setUp(self):
        self.r = Nested.loads(github_return)

    def test_attrs_map(self):
        self.assertEqual(self.r.id, 1)
        self.assertEqual(self.r.name, 'name_test')
        self.assertEqual(self.r.date, datetime(2008, 1, 14, 4, 33, 35))

    def test_MAPS(self):
        self.assertIsInstance(self.r.simple, Simple)
        self.assertEqual(self.r.simple.type, 'simple')

    def test_LIST_collection_map(self):
        has_simple_objects = filter(lambda x: isinstance(x, HasSimple),
                                    self.r.list_collection)
        self.assertEqual(len(has_simple_objects), 2)
        self.assertEqual(self.r.list_collection[0].type, 'has_simple')
        self.assertEqual(self.r.list_collection[0].simple.type, 'simple')

    def test_DICT_collection_map(self):
        arg1_has_simple = self.r.items_collections['arg1']
        self.assertEqual(arg1_has_simple.type, 'has_simple')
        self.assertEqual(arg1_has_simple.simple.type, 'simple')

    def test_SELF_nested(self):
        self.assertIsInstance(self.r.self_nested, Nested)
        self.assertIsInstance(self.r.self_nested.simple, Simple)
        self.assertIsInstance(self.r.list_collection[0], HasSimple)
        self.assertIsInstance(self.r.items_collections['arg1'], HasSimple)

    def test_SELF_nested_in_collections(self):
        self.assertIsInstance(self.r.self_nested_list[0], Nested)
        self.assertIsInstance(self.r.self_nested_dict['arg1'], Nested)


class TestRawResource(TestCase):

    def test_return_original_copy(self):
        self.r = Raw.loads(github_return)
        self.assertEqual(self.r['id'], github_dict['id'])
