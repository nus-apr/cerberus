# -*- encoding: utf-8 -*-

from pygithub3.exceptions import (UriInvalid, RequestDoesNotExist,
    ValidationError, InvalidBodySchema)
from pygithub3.requests.base import Factory, Body, Request
from pygithub3.tests.utils.base import DummyRequest, dummy_json
from pygithub3.tests.utils.core import TestCase
from pygithub3.tests.utils.requests import (RequestWithArgs, RequestCleanedUri,
    RequestBodyInvalidSchema, RequestCleanedBody)


class TestFactory(TestCase):

    def setUp(self):
        self.f = Factory()

    def test_BUILDER_with_invalid_action(self):
        self.assertRaises(UriInvalid, self.f, 'invalid')
        self.assertRaises(UriInvalid, self.f, 'invalid.')
        self.assertRaises(UriInvalid, self.f, '.invalid')

    def test_BUILDER_with_fake_action(self):
        self.assertRaises(RequestDoesNotExist, self.f, 'users.fake')
        self.assertRaises(RequestDoesNotExist, self.f, 'fake.users')

    def test_BUILDER_builds_users(self):
        """ Users.get as real test because it wouldn't be useful mock
        the import-jit process """
        request = self.f('users.get')
        self.assertIsInstance(request, Request)


class TestRequest(TestCase):

    def test_SIMPLE_with_correct_args(self):
        request = RequestWithArgs(arg1='arg1', arg2='arg2')
        self.assertEqual(str(request), 'URI/arg1/arg2')

    def test_SIMPLE_without_needed_args(self):
        request = RequestWithArgs()
        self.assertRaises(ValidationError, str, request)

    def test_with_cleaned_uri(self):
        """ Its real uri has args but I override `clean_uri` method, so
        if `nomatters` arg exists, change uri to `URI` """
        request = RequestCleanedUri(notmatters='test')
        self.assertEqual(str(request), 'URI')

    def test_with_cleaned_body(self):
        self.assertRaises(ValidationError, RequestCleanedBody)

    def test_with_invalid_schema(self):
        self.assertRaises(InvalidBodySchema, RequestBodyInvalidSchema)

    def test_body_without_schema(self):
        request = DummyRequest(body=dict(arg1='test'))
        self.assertEqual(request.get_body(), dict(arg1='test'))
        self.assertEqual(request.body.schema, set(()))
        self.assertEqual(request.body.required, set(()))

    def test_without_body_and_without_schema(self):
        request = DummyRequest()
        self.assertIsNone(request.get_body())


@dummy_json
class TestRequestBodyWithSchema(TestCase):

    def setUp(self):
        valid_body = dict(schema=('arg1', 'arg2'), required=('arg1', ))
        self.b = Body({}, **valid_body)

    def test_with_body_empty_and_schema_permissive(self):
        self.b.schema = ('arg1', 'arg2', '...')
        self.b.required = ()
        self.assertEqual(self.b.dumps(), {})

    def test_with_required(self):
        self.b.content = dict(arg1='arg1')
        self.assertEqual(self.b.dumps(), dict(arg1='arg1'))

    def test_without_required(self):
        self.b.content = dict(arg2='arg2')
        self.assertRaises(ValidationError, self.b.dumps)

    def test_with_invalid(self):
        self.b.content = 'invalid'
        self.assertRaises(ValidationError, self.b.dumps)

    def test_with_body_as_None(self):
        self.b.content = None
        self.assertRaises(ValidationError, self.b.dumps)

    def test_only_valid_keys(self):
        self.b.content = dict(arg1='arg1', arg2='arg2', fake='test')
        self.assertEqual(self.b.dumps(), dict(arg1='arg1', arg2='arg2'))
