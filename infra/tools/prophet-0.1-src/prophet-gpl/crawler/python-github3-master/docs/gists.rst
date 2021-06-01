.. _Gists service:

Gists services
===============

**Fast sample**::

    from pygithub3 import Github

    auth = dict(login='octocat', password='pass')
    gh = Github(**auth)

    octocat_gists = gh.gists.list()
    the_first_gist = gh.gists.get(1)

    the_first_gist_comments = gh.gists.comments.list(1)

Gist
-----

.. autoclass:: pygithub3.services.gists.Gist
    :members:

    .. attribute:: comments

        :ref:`Comments service`

.. _Comments service:

Comments
----------

.. autoclass:: pygithub3.services.gists.Comments
    :members:

.. _github gists doc: http://developer.github.com/v3/gists
.. _github comments doc: http://developer.github.com/v3/gists/comments
