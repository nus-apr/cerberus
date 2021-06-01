all-local: repair.conf localizer-basic.conf localizer-absdir.conf

repair.conf: Makefile.am
	:;{ \
		echo "revision_file=revision.log" && \
		echo "src_dir=src" && \
		echo "test_dir=tests" && \
		echo "build_cmd=$(abs_top_srcdir)/tools/simple-build.py" && \
		echo "test_cmd=$(abs_top_srcdir)/tools/simple-test.py"; \
	} > repair.conf

localizer-basic.conf: Makefile.am
	:;{ \
		echo "revision_file=revision.log" && \
		echo "src_dir=src" && \
		echo "test_dir=tests" && \
		echo "build_cmd=$(abs_top_srcdir)/tools/simple-build.py" && \
		echo "test_cmd=$(abs_top_srcdir)/tools/simple-test.py" && \
		echo "localizer=profile"; \
	} > localizer-basic.conf

localizer-absdir.conf: Makefile.am
	:;{ \
		echo "revision_file=$(abs_top_srcdir)/tests/profile_localizer/basic/revision.log" && \
		echo "src_dir=$(abs_top_srcdir)/tests/profile_localizer/basic/src" && \
		echo "test_dir=$(abs_top_srcdir)/tests/profile_localizer/basic/tests" && \
		echo "build_cmd=$(abs_top_srcdir)/tools/simple-build.py" && \
		echo "test_cmd=$(abs_top_srcdir)/tools/simple-test.py" && \
		echo "localizer=profile"; \
	} > localizer-absdir.conf

php-repair.conf: Makefile.am
	:;{ \
		echo "src_dir=php-src" && \
		echo "dep_dir=$(abs_top_builddir)/benchmarks/php-deps" && \
		echo "build_cmd=$(abs_top_srcdir)/tools/php-build.py" && \
		echo "fixtest_argfile=php-args"; \
	} > php-repair.conf

$(srcdir)/package.m4: $(top_srcdir)/configure.ac
	:;{ \
	  echo "# Signature of the current package." && \
	  echo "m4_define([AT_PACKAGE_NAME],      [@PACKAGE_NAME@])" && \
	  echo "m4_define([AT_PACKAGE_TARNAME],   [@PACKAGE_TARNAME@])" && \
	  echo "m4_define([AT_PACKAGE_VERSION],   [@PACKAGE_VERSION@])" && \
	  echo "m4_define([AT_PACKAGE_STRING],    [@PACKAGE_STRING@])" && \
	  echo "m4_define([AT_PACKAGE_BUGREPORT], [@PACKAGE_BUGREPORT@])" && \
	  echo "m4_define([AT_PACKAGE_URL],       [@PACKAGE_URL@])"; \
	} > $@~
	mv $@~ $@

TESTSUITE_AT = $(srcdir)/testsuite.at

EXTRA_DIST = $(TESTSUITE_AT) $(srcdir)/package.m4 $(TESTSUITE) atlocal.in
TESTSUITE = $(srcdir)/testsuite

PHPCASES = php-case-1056c57f php-case-1056c57f php-case-8ba00176 php-case-efcb9a71 \
	php-case-5a8c917 php-case-2adf58 php-case-991ba131 php-case-1e91069 \
	php-case-f455f8^1-f455f8 

LIBTIFFCASES = libtiff-case-tests-eec7ec0 libtiff-case-tests2-e8a47d4^1-e8a47d4

LIGHTTPDCASES = lighttpd-case-1914

.PHONY: all-cases all-php-cases all-libtiff-cases

all-php-cases: $(PHPCASES)

all-libtiff-cases: $(LIBTIFFCASES)

all-lighttpd-cases: $(LIGHTTPDCASES)

all-cases: all-php-cases all-libtiff-cases all-lighttpd-cases

php-case-% :
	$(abs_top_srcdir)/tools/php-case-create.py $(abs_top_builddir) $(abs_top_srcdir) $*

libtiff-case-%:
	$(abs_top_srcdir)/tools/libtiff-case-create.py $(abs_top_builddir) $(abs_top_srcdir) $*

lighttpd-case-%:
	$(abs_top_srcdir)/tools/lighttpd-case-create.py $(abs_top_builddir) $(abs_top_srcdir) $*

gmp-case-%:
	$(abs_top_srcdir)/tools/gmp-case-create.py $(abs_top_builddir) $(abs_top_srcdir) $*

gzip-case-%:
	$(abs_top_srcdir)/tools/gzip-case-create.py $(abs_top_builddir) $(abs_top_srcdir) $*

python-case-%:
	$(abs_top_srcdir)/tools/python-case-create.py $(abs_top_builddir) $(abs_top_srcdir) $*

wireshark-case-%:
	$(abs_top_srcdir)/tools/wireshark-case-create.py $(abs_top_builddir) $(abs_top_srcdir) $*

fbc-case-%:
	$(abs_top_srcdir)/tools/fbc-case-create.py $(abs_top_builddir) $(abs_top_srcdir) $*

#PHPCASES = php-src-f0c926 php-src-f6ff3a php-src-fc3f8a php-src-ff63c0

#php-src-% :
#	cp -rf $(abs_top_builddir)/benchmarks/php-src $@
#	cd $@ && git checkout -f $*^1
#	$(abs_top_srcdir)/tools/php-build.py -d `head -n 1 $(abs_top_srcdir)/tests/php-fix/cheat-$*` -p $(abs_top_builddir)/benchmarks/php-deps $@ php-args-$*

check-local: atconfig atlocal $(TESTSUITE) $(LINUX)
	$(SHELL) '$(TESTSUITE)' $(TF)

installcheck-local: atconfig atlocal $(TESTSUITE)
	$(SHELL) '$(TESTSUITE)' AUTOTEST_PATH='$(bindir)' $(TF)

clean-local:
	test ! -f '$(TESTSUITE)' || $(SHELL) '$(TESTSUITE)' --clean
	rm -rf __tmp*

AUTOM4TE = $(SHELL) $(top_srcdir)/build-aux/missing --run autom4te
AUTOTEST = $(AUTOM4TE) --language=autotest
$(TESTSUITE): $(TESTSUITE_AT) $(srcdir)/package.m4
	$(AUTOTEST) -I '$(srcdir)' $@.at -o $@~
	mv $@~ $@
