sudo apt update
sudo apt install -y docker.io pypy3 pypy3-dev python3.9 python3.9-distutils gdb make g++ unzip afl++
sudo usermod -aG docker ubuntu
sudo pypy3 -m easy_install docker more_itertools
curl https://bootstrap.pypa.io/get-pip.py -o get-pip.py && python3.9 get-pip.py && rm get-pip.py
python3.9 -m pip install pipenv virtualenv docker

sudo apt-get install -y  \
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
    unzip \
    libasan4 \
    libasan5 \
    libasan6


git clone https://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:x-oauth-basic@github.com/rshariffdeen/cerberus
git clone https://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:x-oauth-basic@github.com/rshariffdeen/valkyrie
git clone https://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:x-oauth-basic@github.com/rshariffdeen/valkyrie-experiments
cd ~;git clone https://github.com/GJDuck/e9patch.git ~/e9patch; cd ~/e9patch; bash build.sh
cd ~; git clone https://github.com/GJDuck/e9afl.git ~/e9afl; cd ~/e9afl; bash build.sh
sudo ln -s ~/e9afl/e9afl /usr/local/bin/e9afl
sudo ln -s ~/e9patch/e9tool /usr/local/bin/e9tool



#git clone https://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:x-oauth-basic@github.com/rshariffdeen/Darjeeling
#python3.9 -m pip install .

docker pull rshariffdeen/cerberus:prophet
docker pull rshariffdeen/cerberus:f1x
docker pull rshariffdeen/cerberus:darjeeling

#/etc/sysctl.conf
#fs.file-max=500000
#
#/etc/security/limits.conf
#*               hard    nofile             10000
#*               soft    nofile             5000
#
#~/.profile
#PATH="$PATH:$HOME/valkyrie/bin:$HOME/cerberus/bin"