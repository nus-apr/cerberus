Documentation Overview
=======================

**pygithub3** is a Github APIv3 python wrapper.

You can consume the API with several :doc:`services` (users, repos...) like
you see in `Github API v3 documentation`_.

When you do an API request, **pygithub3** map the result into :doc:`resources`
which can do its own related requests in future releases.

Fast sample
-----------
::

    from pygithub3 import Github

    gh = Github(login='octocat', password='password')

    octocat = gh.users.get() # Auth required
    copitux = gh.users.get('copitux')
    # copitux = <User (copitux)>

    octocat_followers = gh.users.followers.list().all()
    copitux_followers = gh.users.followers.list('copitux').all()
    # copitux_followers = [<User (ahmontero)>, <User (alazaro)>, ...]


Others
-------

You must apologize my English level. I'm trying to do my best


.. toctree::
    :maxdepth: 3

    installation
    github
    services
    result
    resources

.. _Github API v3 documentation: http://developer.github.com
