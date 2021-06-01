.. _Users service:

Users services
===============

**Fast sample**::

    from pygithub3 import Github

    auth = dict(login='octocat', password='pass')
    gh = Github(**auth)

    # Get copitux user
    gh.users.get('copitux')

    # Get copitux's followers
    gh.users.followers.list('copitux')

    # Get octocat's emails
    gh.users.emails.list()

User
--------

.. autoclass:: pygithub3.services.users.User
    :members:

    .. attribute:: emails

        :ref:`Emails service`
    .. attribute:: keys

        :ref:`Keys service`
    .. attribute:: followers

        :ref:`Followers service`

.. _Emails service:

Emails
--------

.. autoclass:: pygithub3.services.users.Emails
    :members:

.. _Keys service:

Keys
------

.. autoclass:: pygithub3.services.users.Keys
    :members:

.. _Followers service:

Followers
-----------

.. autoclass:: pygithub3.services.users.Followers
    :members:
