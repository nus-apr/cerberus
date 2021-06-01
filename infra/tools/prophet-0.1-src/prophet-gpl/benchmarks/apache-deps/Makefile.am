.PHONY: all-local clean-local

all-local: apr-src apr-util-src apr-build apr-util-build

apr-src:
	svn co http://svn.apache.org/repos/asf/apr/apr/branches/1.5.x apr-src

apr-build: apr-src
	cd apr-src &&\
	./buildconf &&\
	./configure --prefix=$(abs_builddir)/apr-build &&\
	make -j 4 &&\
	make install

apr-util-src:
	svn co http://svn.apache.org/repos/asf/apr/apr-util/branches/1.5.x apr-util-src

apr-util-build: apr-util-src
	cd apr-util-src &&\
	./buildconf --with-apr=../apr-src &&\
	./configure --prefix=$(abs_builddir)/apr-util-build --with-apr=$(abs_builddir)/apr-build &&\
	make -j 4 &&\
	make install

clean-local:
	rm -rf *-build
	rm -rf *-src
