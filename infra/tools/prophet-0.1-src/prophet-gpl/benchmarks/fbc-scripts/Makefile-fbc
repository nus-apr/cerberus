.PHONY: all

all:
	export PATH=`pwd`/fbc-bin/bin:$$PATH && cd fbc-src/src/compiler/obj/linux && make && make install
	export PATH=`pwd`/fbc-bin/bin:$$PATH && cd fbc-src/src/rtlib/obj/linux && export MULTITHREADED= && make && make MULTITHREADED=1 && make install
	export PATH=`pwd`/fbc-bin/bin:$$PATH && cd fbc-src/src/gfxlib2/obj/linux && make && make install
	export PATH=`pwd`/fbc-bin/bin:$$PATH && cd fbc-src && ./install.sh -i
