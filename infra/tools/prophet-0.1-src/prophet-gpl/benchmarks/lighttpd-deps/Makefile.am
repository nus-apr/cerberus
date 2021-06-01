.PHONY: all-local clean-local

all-local: pcre-8.36-build libxml2-2.7.2-build sqlite3-build

pcre-8.36-build:
	wget ftp://ftp.csx.cam.ac.uk/pub/software/programming/pcre/pcre-8.36.tar.gz
	tar xvzf pcre-8.36.tar.gz
	cd pcre-8.36 &&\
	./configure --prefix=$(abs_builddir)/pcre-8.36-build &&\
	make -j 4 &&\
	make install

libxml2-2.7.2-build:
	wget ftp://xmlsoft.org/libxml2/libxml2-2.7.2.tar.gz
	tar xvzf libxml2-2.7.2.tar.gz
	cd libxml2-2.7.2 &&\
	./configure --prefix=$(abs_builddir)/libxml2-2.7.2-build &&\
	make -j 4 &&\
	make install

sqlite3-build:
	wget http://www.sqlite.org/2014/sqlite-autoconf-3080600.tar.gz
	tar xvzf sqlite-autoconf-3080600.tar.gz
	cd sqlite-autoconf-3080600 &&\
	./configure --prefix=$(abs_builddir)/sqlite3-build &&\
	make -j 4 &&\
	make install

clean-local:
	rm *.gz
	rm -rf *-build
	rm -rf pcre-8.36
