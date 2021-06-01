## Process this file with automake to create Makefile.in
# Copyright 2010 Free Software Foundation, Inc.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3, or (at your option)
# any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

TESTS =					\
  helin-segv				\
  hufts					\
  memcpy-abuse				\
  mixed					\
  null-suffix-clobber			\
  stdin					\
  trailing-nul				\
  zdiff					\
  zgrep-f				\
  zgrep-signal				\
  znew-k

EXTRA_DIST =				\
  $(TESTS)				\
  init.cfg				\
  init.sh				\
  hufts-segv.gz

built_programs = \
  gzip		\
  gunzip	\
  gzexe		\
  zcat		\
  zcmp		\
  zdiff		\
  zegrep	\
  zfgrep	\
  zforce	\
  zgrep		\
  zless		\
  zmore		\
  znew

TESTS_ENVIRONMENT =				\
  tmp__=$$TMPDIR; test -d "$$tmp__" || tmp__=.;	\
  TMPDIR=$$tmp__; export TMPDIR;		\
  shell_or_perl_() {				\
    if grep '^\#!/usr/bin/perl' "$$1" > /dev/null; then			\
      if $(PERL) -e 'use warnings' > /dev/null 2>&1; then		\
	grep '^\#!/usr/bin/perl -T' "$$1" > /dev/null && T_=T || T_=;	\
        $(PERL) -w$$T_ -I$(srcdir) -MCoreutils				\
	      -M"CuTmpdir qw($$f)" -- "$$1";	\
      else					\
	echo 1>&2 "$$tst: configure did not find a usable version of Perl," \
	  "so skipping this test";		\
	(exit 77);				\
      fi;					\
    else					\
      $(SHELL) "$$1";				\
    fi;						\
  };						\
  LC_ALL=C; export LC_ALL;						\
  VERSION=$(VERSION); export VERSION;					\
  abs_top_builddir='$(abs_top_builddir)'; export abs_top_builddir;	\
  abs_top_srcdir='$(abs_top_srcdir)'; export abs_top_srcdir;		\
  abs_srcdir='$(abs_srcdir)'; export abs_srcdir;			\
  built_programs='$(built_programs)'; export built_programs;		\
  srcdir='$(srcdir)'; export srcdir;					\
  top_srcdir='$(top_srcdir)'; export top_srcdir;			\
  CC='$(CC)'; export CC;						\
  GREP='$(GREP)'; export GREP;						\
  GZIP_TEST_NAME=`echo $$tst|sed 's,^\./,,;s,/,-,g'`; export GZIP_TEST_NAME; \
  MAKE=$(MAKE); export MAKE;						\
  PACKAGE_BUGREPORT='$(PACKAGE_BUGREPORT)'; export PACKAGE_BUGREPORT;	\
  PACKAGE_VERSION=$(PACKAGE_VERSION); export PACKAGE_VERSION;		\
  PERL='$(PERL)'; export PERL;						\
  SHELL='$(SHELL)'; export SHELL;					\
  PATH='$(abs_top_builddir)$(PATH_SEPARATOR)'"$$PATH"; export PATH;	\
  9>&2

VERBOSE = yes
