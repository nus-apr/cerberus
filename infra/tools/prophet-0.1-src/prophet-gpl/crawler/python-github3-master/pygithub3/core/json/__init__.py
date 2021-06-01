# -*- coding: utf-8 -*-
"""
Emulate json module with encode/decoders to support github datetime format
"""

from datetime import datetime
try:
    import simplejson as json
except ImportError:
    import json

GITHUB_DATE_FORMAT = '%Y-%m-%dT%H:%M:%SZ'


class GHJSONEncoder(json.JSONEncoder):
    def default(self, o):
        try:
            return datetime.strftime(o, GITHUB_DATE_FORMAT)
        except:
            return super(GHJSONEncoder, self).default(o)


def gh_decoder_hook(dict_):
    for k, v in dict_.iteritems():
        try:
            date = datetime.strptime(v, GITHUB_DATE_FORMAT)
            dict_[k] = date
        except:
            continue
    return dict_


def dumps(obj, cls=GHJSONEncoder, **kwargs):
    return json.dumps(obj, cls=cls, **kwargs)


def loads(s, object_hook=gh_decoder_hook, **kwargs):
    return json.loads(s, object_hook=object_hook, **kwargs)

dump = json.dump
load = json.load
