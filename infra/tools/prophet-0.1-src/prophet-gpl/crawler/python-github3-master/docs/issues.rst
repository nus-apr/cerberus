.. _Issues service:

Issues services
===============

**Fast sample**::

    from pygithub3 import Github

    auth = dict(login='octocat', password='pass')
    gh = Github(**auth)

    octocat_issues = gh.issues.list()
    octocat_repo_issues = gh.issues.list_by_repo('octocat', 'Hello-World')

Issues
------

.. autoclass:: pygithub3.services.issues.Issue
    :members:

    .. attribute:: comments

        :ref:`Issues comments service`

    .. attribute:: events

        :ref:`Issues events service`

    .. attribute:: labels

        :ref:`Labels service`

    .. attribute:: milestones

        :ref:`Milestones service`

.. _Issues comments service:

Comments
--------

.. autoclass:: pygithub3.services.issues.Comments
    :members:

.. _Issues events service:

Events
------

.. autoclass:: pygithub3.services.issues.Events
    :members:

.. _Labels service:

Labels
------

.. autoclass:: pygithub3.services.issues.Labels
    :members:

.. _Milestones service:

Milestones
----------

.. autoclass:: pygithub3.services.issues.Milestones
    :members:

.. _github issues doc: http://developer.github.com/v3/issues
.. _github comments doc: http://developer.github.com/v3/issues/comments
.. _github events doc: http://developer.github.com/v3/issues/events
.. _github labels doc: http://developer.github.com/v3/issues/labels
.. _github milestones doc: http://developer.github.com/v3/issues/milestones
