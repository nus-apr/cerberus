sudo apt update
sudo apt-get install -y  \
    afl++ \
    automake \
    autopoint \
    bison \
    docker.io \
    flex \
    g++ \
    g++-multilib \
    gcc-multilib \
    gdb \
    gettext \
    git \
    gperf \
    libasan4 \
    libasan5 \
    libasan6 \
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
    make \
    mercurial \
    nasm \
    nano \
    pkg-config \
    psmisc \
    pypy3 \
    pypy3-dev \
    python3 \
    python3.9 \
    python3.9-distutils \
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
    tk-dev \
    tcl-dev \
    tix-dev \
    unzip

sudo usermod -aG docker ubuntu
sudo pypy3 -m easy_install docker more_itertools
curl https://bootstrap.pypa.io/get-pip.py -o get-pip.py && python3.9 get-pip.py && rm get-pip.py
python3.9 -m pip install pipenv virtualenv docker


git clone https://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:x-oauth-basic@github.com/rshariffdeen/cerberus
git clone https://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:x-oauth-basic@github.com/rshariffdeen/valkyrie
#git clone https://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:x-oauth-basic@github.com/rshariffdeen/valkyrie-experiments
git clone https://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:x-oauth-basic@github.com/rshariffdeen/cfr-experiments
cd ~;git clone https://github.com/GJDuck/e9patch.git ~/e9patch; cd ~/e9patch; bash build.sh
cd ~; git clone https://github.com/GJDuck/e9afl.git ~/e9afl; cd ~/e9afl; bash build.sh
sudo ln -s ~/e9afl/e9afl /usr/local/bin/e9afl
sudo ln -s ~/e9patch/e9tool /usr/local/bin/e9tool



#git clone https://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:x-oauth-basic@github.com/rshariffdeen/Darjeeling
#python3.9 -m pip install .

docker pull rshariffdeen/cerberus:prophet
docker pull rshariffdeen/cerberus:f1x
docker pull rshariffdeen/cerberus:darjeeling

sudo sed -i -e '$afs.file-max=500000' /etc/sysctl.conf
sudo sed -i -e '$a*               hard    nofile             1000000' /etc/security/limits.conf
sudo sed -i -e '$a*               soft    nofile             100000' /etc/security/limits.conf
sudo sed -i -e '$aPATH="$PATH:$HOME/valkyrie/bin:$HOME/cerberus/bin"'  ~/.profile
source ~/.profile


