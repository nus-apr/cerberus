SUBDIRS = php-deps libtiff-deps lighttpd-deps apache-deps

all-local: php-src lighttpd-src libtiff-src libtiff-tests libtiff-tests2 gmp-src gmp-tests gzip-src gzip-tests python-src python-tests wireshark-src wireshark-tests apr-src httpd-src subversion-src curl-src

php-src :
	git clone https://github.com/php/php-src.git php-src

lighttpd-src:
	svn checkout svn://svn.lighttpd.net/lighttpd/trunk/ lighttpd-src

libtiff-src:
	git clone https://github.com/vadz/libtiff.git libtiff-src

libtiff-tests: libtiff-src
	cp -rf libtiff-src libtiff-src-tmp
	cd libtiff-src-tmp && git checkout -f 76ac713a && git clean -f -d
	$(abs_top_srcdir)/tools/libtiff-build.py -x libtiff-src-tmp
	cp -rf libtiff-src-tmp/test libtiff-tests
	cp -f $(srcdir)/libtiff-myscript/common.sh libtiff-tests/
	cp -f $(srcdir)/libtiff-myscript/smart-diff.py libtiff-tests/
	rm -rf libtiff-src-tmp

libtiff-tests2: libtiff-tests
	cp -rf libtiff-tests libtiff-tests2
	cp -f $(srcdir)/libtiff-myscript/rewrite_tag.c libtiff-tests2/

gmp-src:
	hg clone https://gmplib.org/repo/gmp gmp-src

gmp-tests: gmp-src
	cp -rf gmp-src gmp-src-tmp
	cd gmp-src-tmp && hg update -r 14177 -C
	$(abs_top_srcdir)/tools/gmp-build.py gmp-src-tmp
	cp -rf gmp-src-tmp/tests gmp-tests
	rm -rf gmp-src-tmp

gzip-src:
	git clone http://git.savannah.gnu.org/cgit/gzip.git gzip-src

gzip-tests: gzip-src
	cp -rf gzip-src gzip-src-tmp
	cd gzip-src-tmp && git checkout -f ab9eb0da6e773
	cp -rf $(srcdir)/gzip-scripts/Makefile.am gzip-src-tmp/tests/Makefile.am
	cp -rf $(srcdir)/gzip-scripts/hufts gzip-src-tmp/tests/hufts
	$(abs_top_srcdir)/tools/gzip-build.py gzip-src-tmp
	cp -rf gzip-src-tmp/tests gzip-tests
	chmod a+x gzip-tests/mixed
	chmod a+x gzip-tests/zgrep-f
	chmod a+x gzip-tests/zgrep-signal
	chmod a+x gzip-tests/znew-k
	$(srcdir)/gzip-scripts/makefile-clean.py gzip-tests/Makefile
	if [ -f gzip-src-tmp/build-aux/test-driver ] ; \
	then \
		cp -f gzip-src-tmp/build-aux/test-driver gzip-tests/test-driver; \
	fi;
	rm -rf gzip-src-tmp

python-src:
	hg clone https://hg.python.org/cpython/ python-src

python-tests: python-src
	cp -rf python-src python-src-tmp
	cd python-src-tmp && hg update -r 70300 -C
	cp -rf python-src-tmp/Lib/test python-tests
	rm -rf python-src-tmp

wireshark-src:
	git clone https://code.wireshark.org/review/wireshark wireshark-src

wireshark-tests: wireshark-src
	cp -rf wireshark-src wireshark-src-tmp
	cd wireshark-src-tmp && git checkout -f 4b7cc99d
	cp -rf wireshark-src-tmp/test wireshark-tests
	cp -f $(srcdir)/wireshark-scripts/mytest.sh wireshark-tests/mytest.sh
	cp -f $(srcdir)/wireshark-scripts/services wireshark-tests/services
	rm -rf wireshark-src-tmp

fbc-src:
	mkdir fbc-src
	cd fbc-src && svn co https://fbc.svn.sourceforge.net/svnroot/fbc/trunk/FreeBASIC fbc-src
	cp -f $(srcdir)/fbc-scripts/Makefile-fbc fbc-src/Makefile
	cp -f $(srcdir)/fbc-scripts/configure-fbc fbc-src/configure
	cp -f $(srcdir)/fbc-scripts/fbc-bin.tar.gz fbc-src/
	cd fbc-src && tar xvzf fbc-bin.tar.gz && rm fbc-bin.tar.gz && mv FreeBASIC-1.00.0-linux-x86 fbc-bin

fbc-tests: fbc-src
	cp -rf fbc-src fbc-src-tmp
	cd fbc-src-tmp/fbc-src && svn update -r 5565
	cp -rf fbc-src-tmp/fbc-src/tests fbc-tests
	cp -f $(srcdir)/fbc-scripts/fbc-run-tests.pl fbc-tests/
	rm -rf fbc-src-tmp

apr-src:
	svn co http://svn.apache.org/repos/asf/apr/apr/trunk apr-src

httpd-src:
	svn co http://svn.apache.org/repos/asf/httpd/httpd/trunk httpd-src

subversion-src:
	svn co http://svn.apache.org/repos/asf/subversion/trunk subversion-src

curl-src:
	git clone https://github.com/bagder/curl.git curl-src

clean-local:
	rm -rf php-src
	rm -rf lighttpd-src
	rm -rf libtiff-src
	rm -rf libtiff-tests
	rm -rf libtiff-tests2
	rm -rf gmp-tests
	rm -rf gzip-src
	rm -rf gzip-tests
	rm -rf python-src
	rm -rf python-tests
	rm -rf fbc-src
	rm -rf apr-src
	rm -rf httpd-src
	rm -rf subversion-src
	rm -rf curl-src
