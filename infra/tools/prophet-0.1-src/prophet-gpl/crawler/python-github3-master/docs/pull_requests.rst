.. _Pull Requests service:

Pull Requests service
=====================

**Example**::

    from pygithub3 import Github

    gh = Github(user='octocat', repo='sample')

    pull_requests = gh.pull_requests.list().all()
    pull_request_commits = gh.pull_requests.list_commits(2512).all()

Pull Requests
-------------

.. autoclass:: pygithub3.services.pull_requests.PullRequests
    :members:

    .. attribute:: comments

        :ref:`Pull Request Comments service`


.. _Pull Request Comments service:

Pull Request Comments
---------------------

.. autoclass:: pygithub3.services.pull_requests.Comments
    :members:

.. _github pullrequests doc: http://developer.github.com/v3/pulls
.. _github pullrequests comments doc: http://developer.github.com/v3/pulls/comments
