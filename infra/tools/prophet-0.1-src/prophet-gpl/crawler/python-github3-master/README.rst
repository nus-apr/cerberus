.. image:: https://secure.travis-ci.org/copitux/python-github3.png

Pygithub3
==========

Pygithub3 is a wrapper to the **Github API v3**,
written in Python.

It has been developed with extensibility in mind, because the ``API`` is in a
beta state, trying to achieve a very loosly coupled software.

It should be very easy to extend to support new ``requests`` and ``resources``,
because each of them are managed by itself.

`Pygithub3 docs <http://pygithub3.rtfd.org>`_

`Github API v3 docs <http://developer.github.com/v3/>`_

Fast install
-------------
::

    pip install pygithub3

Fast example
-------------
::

    from pygithub3 import Github

    gh = Github(login='copitux', password='password')

    copitux = gh.users.get()
    kennethreitz = gh.users.get('kennethreitz')

    copitux_repos = gh.repos.list().all()
    kennethreitz_repos = gh.repos.list('kennethreitz').all()

Achievements
-------------

- The core
- `Users service <http://developer.github.com/v3/users/>`_
- `Repos service <http://developer.github.com/v3/repos/>`_
- `Gists service <http://developer.github.com/v3/gists/>`_
- `Git Data service <http://developer.github.com/v3/git/>`_
- `Pull requests service <http://developer.github.com/v3/pulls/>`_
- `Orgs service <http://developer.github.com/v3/orgs/>`_
- `Issues service <http://developer.github.com/v3/issues/>`_
- `Events service <http://developer.github.com/v3/events/>`_

TODO
-----

- Oauth authorization API (service?)
- Proxy methods into resources (e.g copitux.followers)

Contribute
-----------

1. Fork the `repository <https://github.com/copitux/python-github3>`_
2. Write a test to cover new feature or to reproduce bug
3. Code with `pep8 <http://www.python.org/dev/peps/pep-0008/>`_ rules
4. Add yourself to ``AUTHORS``
5. Pull request it to ``develop`` branch

Tests
-----

Run ``make init`` to install test requirements and ``nosetests`` to run tests.
