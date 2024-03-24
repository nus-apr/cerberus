FROM ubuntu:18.04
LABEL maintainer="Ridwan Shariffdeen <rshariffdeen@gmail.com>"

RUN apt-get update && apt-get upgrade -y && apt-get autoremove -y

# install experiment dependencies
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends  \
    ant \
    automake \
    autopoint \
    bison \
    flex \
    g++-multilib \
    gcc-multilib \
    gettext \
    git \
    gperf \
    libfreetype6 \
    libfreetype6-dev \
    libgdbm-dev \
    libglib2.0-dev \
    libguice-java \
    libpython-dev \
    libpython3-dev \
    libtool \
    libvdpau-dev \
    m4 \
    maven \
    mercurial \
    nano \
    nasm \
    openjdk-11-jdk \
    openjdk-11-jdk-headless \
    pkg-config \
    psmisc \
    python3 \
    subversion \
    tcl-dev \
    texinfo \
    tix-dev \
    tk-dev \
    unzip \
    xutils-dev \
    yasm
