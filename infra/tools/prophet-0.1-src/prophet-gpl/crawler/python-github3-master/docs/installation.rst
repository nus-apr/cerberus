Installation
=============
::

    pip install pygithub3

    or

    easy_install pygithub3


Dependencies
---------------

Required
.........

This library depends only on the `requests`_ module.

If you install ``pygithub3`` with ``pip`` all is done. This is the best option.

Optional
.........

The test suite uses `nose`_, `mock`_, and `unittest2`_ (python 2.6). Compiling
the documentation requires `sphinx`_.

Install all of these by running ``pip install -r test_requirements.txt``.  Then
just run ``nosetests`` to run the tests.

.. _requests: http://docs.python-requests.org/en/v0.10.6/index.html
.. _nose: http://readthedocs.org/docs/nose/en/latest
.. _mock: http://pypi.python.org/pypi/mock
.. _unittest2: http://pypi.python.org/pypi/unittest2
.. _sphinx: http://sphinx.pocoo.org/
