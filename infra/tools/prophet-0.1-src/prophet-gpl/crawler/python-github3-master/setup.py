#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from os.path import join

from setuptools import setup, find_packages
import pygithub3

# Odd hack to get 'python setup.py test' working on py2.7
try:
    import multiprocessing
    import logging
except ImportError:
    pass

setup(
    name=pygithub3.__name__,
    version=pygithub3.__version__,
    author=pygithub3.__author__,
    author_email=pygithub3.__email__,
    url='https://github.com/copitux/python-github3',
    description='Python wrapper for the github v3 api',
    long_description=open('README.rst').read(),
    license='ISC',
    packages=find_packages(exclude=['*tests*']),
    test_suite='nose.collector',
    tests_require=[
        'nose',
        'mock',
    ],
    install_requires=map(str.strip, open(join('requirements', 'base.txt'))),
    include_package_data=True,
    classifiers=(
        'Programming Language :: Python',
        'Programming Language :: Python :: 2.6',
        'Programming Language :: Python :: 2.7',
        'License :: OSI Approved :: ISC License (ISCL)',
        'Operating System :: OS Independent',
        'Development Status :: 2 - Pre-Alpha',
        'Intended Audience :: Developers',
    ),
)
