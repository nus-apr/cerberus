.. _Orgs service:

Orgs services
==============

**Fast sample**::

    from pygithub3 import Github

    gh = Github(token='abc123')

    auth_orgs = gh.orgs.list().all()
    members = gh.orgs.members.list('github')

Org
------

.. autoclass:: pygithub3.services.orgs.Org
    :members:

    .. attribute:: members

        :ref:`Members service`

    .. attribute:: teams

        :ref:`Teams service`

.. _Members service:

Members
---------

.. autoclass:: pygithub3.services.orgs.members.Members
    :members:

.. _Teams service:

Teams
-------

.. autoclass:: pygithub3.services.orgs.teams.Teams
    :members:

.. _github orgs doc: http://developer.github.com/v3/orgs
.. _github orgs teams doc: http://developer.github.com/v3/orgs/teams
