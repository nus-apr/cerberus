.PHONY: all-local clean-local

all-local: apr-1.5.1-build apr-util-1.5.3-build

apr-1.5.1-build:
	wget http://mirrors.ibiblio.org/apache/apr/apr-1.5.1.tar.gz
	tar xvzf apr-1.5.1.tar.gz
	cd apr-1.5.1 &&\
	./configure --prefix=$(abs_builddir)/apr-1.5.1-build &&\
	make -j 4 &&\
	make install

apr-util-1.5.3-build: apr-1.5.1-build
	wget http://mirrors.ibiblio.org/apache/apr/apr-util-1.5.3.tar.gz
	tar xvzf apr-util-1.5.3.tar.gz
	cd apr-util-1.5.3 &&\
	./configure --prefix=$(abs_builddir)/apr-util-1.5.3-build --with-apr=$(abs_builddir)/apr-1.5.1-build &&\
	make -j 4 &&\
	make install


clean-local:
	rm *.gz
	rm -rf *-build
	rm -rf apr-1.5.1
	rm -rf apr-util-1.5.3


