.. _Events service:

Events service
==============

This service exposes the `Events API`_. Much of this API is read-only, and while
pagination is supported, there is a fixed page size of 30 with a limit of 10
page requests.

Many events have an `actor` which denotes the user that performed an event.
Additionally, there may be `org` or `repo` attributes for events related to
Organizations and Repos. Finally, each event object contains a `payload`
attribute containing more detailed information about the event.

.. _public events:

Public Events
-------------
Yields the most recent public events from Github.

::

    from pygithub3 import Github

    gh = Github()

    events = gh.events.list().all()
    print events[0].payload

Event
.......

.. autoclass:: pygithub3.services.events.Event
    :members:

    .. attribute:: issues

        :ref:`Issues events <Issues events service>`

    .. attribute:: networks

        :ref:`Events network service`

    .. attribute:: orgs

        :ref:`Events org service`

    .. attribute:: repos

        :ref:`Events repo service`

    .. attribute:: users

        :ref:`Events user service`

.. _repository events:

Repo Events
-----------

These are events for a specific repo, including issue and network events. The
Issues events are proxied to the :ref:`Issues service`.

::

    events = gh.events.repos.list(user="copitux", repo="python-github3")
    for e in events.next():
        print("{t}".format(t=e.type))

    # Get the issue Events
    events = gh.events.issues.list_by_repo(user="copitux",
                                           repo="python-github3")

    # Get the Public Events for a Repo's Network
    events = gh.events.networks.list(user="copitux", repo="python-github3")

.. _Events network service:

Network
.......

.. autoclass:: pygithub3.services.events.networks.Network
    :members:


.. _Events repo service:

Repo
........

.. autoclass:: pygithub3.services.events.repos.Repo
    :members:


.. _organziation events:

Organization Events
-------------------

These are the public events for an Organization

::

    events = gh.events.orgs.list(org="Acme")

You may also get a user's feed of events for an Organization, but you *must* be
authenticated as the provided user, and you must be a member of the given
organization.

::

    events = gh.events.users.orgs(user="copitux", org="acme")

.. _Events org service:

Org
........

.. autoclass:: pygithub3.services.events.orgs.Org
    :members:

.. _user events:

User Events
-----------

You can retrieve the public events performed by a user and the public events
that a user receives. If you're authenticated, you may also receive private
events.

::

    received_events = gh.events.users.list_received_public(user="copitux")
    performed_events = gh.events.users.list_performed_public(user="copitux")

If authenticated as `copitux`, you could get private events with the
following, otherwise you'll just get the public events as above:

::

    received_events = gh.events.users.list_received(user="copitux")
    performed_events = gh.events.users.list_performed(user="copitux")

.. _Events user service:

User
........

.. autoclass:: pygithub3.services.events.users.User
    :members:
