FROM rshariffdeen/cpr:18.04
MAINTAINER Ridwan Shariffdeen <ridwan@comp.nus.edu.sg>
ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get upgrade -y && apt-get autoremove -y

# install experiment dependencies
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends  \
    autopoint \
    automake \
    bison \
    flex \
    gettext \
    gperf \
    libass-dev \
    libfreetype6 \
    libfreetype6-dev \
    libjpeg-dev \
    libtool \
    libxml2-dev \
    liblzma-dev \
    nasm \
    pkg-config \
    texinfo \
    yasm \
    xutils-dev \
    libpciaccess-dev \
    libpython-dev \
    libpython3-dev \
    libx11-dev \
    libxcb-xfixes0-dev \
    libxcb1-dev \
    libxcb-shm0-dev \
    libsdl1.2-dev  \
    libsqlite3-dev \
    libvdpau-dev \
    libnuma-dev \
    shc \
    m4 \
    libglib2.0-dev \
    libldap-dev \
    libbz2-dev \
    libssl-dev \
    libsqlite3-dev \
    libxml2-dev \
    libgdbm-dev \
    subversion \
    libc6-dev-i386 \
    mercurial \
    libncurses-dev \
    libsqlite-dev \
    libgdbm-dev \
    libssl-dev \
    libreadline-gplv2-dev \
    libbz2-dev \
    psmisc \
    libsqlite3-dev \
    gcc-multilib \
    g++-multilib \
    tk-dev \
    mercurial \
    tcl-dev \
    tix-dev \
    libgdbm-compat-dev \
    unzip

# Compile PHP dependencies from source

RUN mkdir -p /deps/php && cd /deps/php
RUN cd /deps/php && wget http://ftp.gnu.org/gnu/autoconf/autoconf-2.13.tar.gz && \
        tar xvzf autoconf-2.13.tar.gz && \
        cd autoconf-2.13 && \
        ./configure --prefix=/deps/php/autoconf-2.13-build && \
        make -j`nproc` && make install

RUN cd /deps/php &&  wget http://ftp.gnu.org/gnu/bison/bison-2.5.1.tar.gz && \
        tar xvzf bison-2.5.1.tar.gz && \
        cd bison-2.5.1 && \
        ./configure --prefix=/deps/php/bison-2.5.1-build && \
        make -j`nproc` && make install

RUN cd /deps/php &&  wget ftp://ftp.gnu.org/gnu/bison/bison-2.2.tar.gz && \
        tar xvzf bison-2.2.tar.gz && \
        cd bison-2.2 && \
        ./configure --prefix=/deps/php/bison-2.2-build && \
        make -j`nproc` && make install

RUN mkdir /experiment
WORKDIR /experiment
