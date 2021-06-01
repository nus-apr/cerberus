.. _Git Data service:

Git Data services
=================

**Example**::

  from pygithub3 import Github

  gh = Github(user='someone', repo='some_repo')

  a_blob = gh.git_data.blobs.get('a long sha')

  dev_branch = gh.git_data.references.get('heads/add_a_thing')


GitData
-------

.. autoclass:: pygithub3.services.git_data.GitData
    :members:

    .. attribute:: blobs

        :ref:`Blobs service`

    .. attribute:: commits

        :ref:`Gitdata commits service`

    .. attribute:: references

        :ref:`References service`

    .. attribute:: tags

        :ref:`Tags service`

    .. attribute:: trees

        :ref:`Trees service`


.. _Blobs service:

Blobs
-----

.. autoclass:: pygithub3.services.git_data.Blobs
    :members:


.. _Gitdata commits service:

Commits
-------

.. autoclass:: pygithub3.services.git_data.Commits
    :members:


.. _References service:

References
----------

.. autoclass:: pygithub3.services.git_data.References
    :members:


.. _Tags service:

Tags
----

.. autoclass:: pygithub3.services.git_data.Tags
    :members:


.. _Trees service:

Trees
-----

.. autoclass:: pygithub3.services.git_data.Trees
    :members:

.. _github commits doc: http://developer.github.com/v3/git/commits
.. _github refs doc: http://developer.github.com/v3/git/refs
.. _github tags doc: http://developer.github.com/v3/git/tags
.. _github trees doc: http://developer.github.com/v3/git/trees
