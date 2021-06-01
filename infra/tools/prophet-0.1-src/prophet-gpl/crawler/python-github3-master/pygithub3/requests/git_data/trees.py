from pygithub3.requests.base import Request
from pygithub3.resources.git_data import Tree


class Get(Request):
    uri = 'repos/{user}/{repo}/git/trees/{sha}'
    resource = Tree


class Create(Request):
    uri = 'repos/{user}/{repo}/git/trees'
    resource = Tree
    body_schema = {
        'schema': ('tree', 'base_tree'),
        'required': ('tree',),
    }
