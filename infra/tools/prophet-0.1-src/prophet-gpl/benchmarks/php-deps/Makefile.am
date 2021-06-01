.PHONY: all-local clean-local

all-local: libxml2-2.7.2-build bison-2.2-build bison-2.5.1-build flex-2.5.4-build autoconf-2.13-build

libxml2-2.7.2-build:
	wget ftp://xmlsoft.org/libxml2/libxml2-2.7.2.tar.gz
	tar xvzf libxml2-2.7.2.tar.gz
	cd libxml2-2.7.2 &&\
	./configure --prefix=$(abs_builddir)/libxml2-2.7.2-build &&\
	make -j 4 &&\
	make install

bison-2.5.1-build:
	wget http://ftp.gnu.org/gnu/bison/bison-2.5.1.tar.gz
	tar xvzf bison-2.5.1.tar.gz
	cd bison-2.5.1 && \
	./configure --prefix=$(abs_builddir)/bison-2.5.1-build && \
	make -j 4 && \
	make install

flex-2.5.4-build:
	cp $(srcdir)/flex-2.5.4a.tar.gz flex-2.5.4a.tar.gz
	tar xvzf flex-2.5.4a.tar.gz
	cd flex-2.5.4 && \
	./configure --prefix=$(abs_builddir)/flex-2.5.4-build && \
	make -j 4 && \
	make install

flex-2.5.39-build:
	cp $(srcdir)/flex-2.5.39.tar.gz flex-2.5.39.tar.gz
	tar xvzf flex-2.5.39.tar.gz
	cd flex-2.5.39 && \
	./configure --prefix=$(abs_builddir)/flex-2.5.39-build && \
	make -j 4 && \
	make install

bison-2.2-build:
	wget ftp://ftp.gnu.org/gnu/bison/bison-2.2.tar.gz
	tar xvzf bison-2.2.tar.gz
	cd bison-2.2 && \
	./configure --prefix=$(abs_builddir)/bison-2.2-build && \
	make -j 4 && \
	make install

autoconf-2.13-build:
	wget http://ftp.gnu.org/gnu/autoconf/autoconf-2.13.tar.gz
	tar xvzf autoconf-2.13.tar.gz
	cd autoconf-2.13 && \
	./configure --prefix=$(abs_builddir)/autoconf-2.13-build && \
	make -j 4 && \
	make install

clean-local:
	rm *.gz
	rm -rf *-build
	rm -rf libxml2-2.7.2
	rm -rf bison-2.5.1
	rm -rf bison-2.2
	rm -rf autoconf-2.13
