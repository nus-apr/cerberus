# -*- coding: utf-8 -*-

from pygithub3.core import json


class Resource(object):

    _dates = ()
    _maps = {}
    _collection_maps = {}

    def __init__(self, attrs):
        self._attrs = attrs
        self.__set_attrs()

    def __set_attrs(self):
        for attr in self._attrs:
            setattr(self, attr, self._attrs[attr])

    def __str__(self):
        return "<%s>" % self.__class__.__name__

    def __repr__(self):
        return self.__str__()

    @classmethod
    def loads(self, json_content):
        resource_chunk = json.loads(json_content)
        if not hasattr(resource_chunk, 'items'):
            return [self.__load(raw_resource)
                    for raw_resource in resource_chunk]
        else:
            return self.__load(resource_chunk)

    @classmethod
    def __load(self, raw_resource):
        def self_resource(func):
            def wrapper(resource, raw_resource):
                if resource == 'self':
                    resource = self
                return func(resource, raw_resource)
            return wrapper

        @self_resource
        def parse_map(resource, raw_resource):
            if hasattr(raw_resource, 'items'):
                return resource.__load(raw_resource)

        @self_resource
        def parse_collection_map(resource, raw_resources):
            # Dict of resources (Ex: Gist file)
            if hasattr(raw_resources, 'items'):
                dict_map = {}
                for key, raw_resource in raw_resources.items():
                    dict_map[key] = resource.__load(raw_resource)
                return dict_map
            # list of resources
            elif hasattr(raw_resources, '__iter__'):
                return [resource.__load(raw_resource)
                        for raw_resource in raw_resources]

        new_resource = raw_resource.copy()
        new_resource.update(dict([
            (attr, parse_map(resource, raw_resource[attr]))
             for attr, resource in self._maps.items()
             if attr in raw_resource]))
        new_resource.update(dict([
            (attr, parse_collection_map(resource, raw_resource[attr]))
             for attr, resource in self._collection_maps.items()
             if attr in raw_resource]))

        return self(new_resource)


class Raw(Resource):

    @classmethod
    def loads(self, json_content):
        return json.loads(json_content)
