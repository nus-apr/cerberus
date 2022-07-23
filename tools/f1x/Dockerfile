FROM rshariffdeen/f1x
MAINTAINER Ridwan Shariffdeen <rshariffdeen@gmail.com>

RUN apt-get update && apt-get upgrade -y && apt-get autoremove -y

# install experiment dependencies
RUN apt-get update && apt-get install -y  \
    automake \
    autopoint \
    bison \
    flex \
    gettext \
    git \
    gperf \
    libass-dev \
    libfreetype6 \
    libfreetype6-dev \
    libjpeg-dev \
    liblzma-dev \
    libnuma-dev \
    libpciaccess-dev \
    libpython-dev \
    libpython3-dev \
    libsdl1.2-dev  \
    libsqlite3-dev \
    libtool \
    libvdpau-dev \
    libx11-dev \
    libxcb-xfixes0-dev \
    libxcb1-dev \
    libxcb-shm0-dev \
    libxml2-dev \
    nasm \
    nano \
    pkg-config \
    psmisc \
    python3 \
    texinfo \
    xutils-dev \
    yasm \
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

# Install cerberus dependencies
RUN apt install -y software-properties-common &&  add-apt-repository -y ppa:pypy/ppa && apt update && apt install -y pypy3 pypy3-dev

RUN mkdir /experiment
WORKDIR /experiment

ENV CC=f1x-cc
ENV CXX=f1x-cxx
