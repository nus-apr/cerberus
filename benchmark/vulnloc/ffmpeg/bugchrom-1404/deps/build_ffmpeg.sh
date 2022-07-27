mkdir /ffmpeg_deps
cd /ffmpeg_deps

wget https://www.alsa-project.org/files/pub/lib/alsa-lib-1.1.0.tar.bz2
git clone --depth 1 --branch libdrm-2.4.100 git://anongit.freedesktop.org/mesa/drm
git clone https://github.com/mstorsjo/fdk-aac.git
wget https://sourceforge.net/projects/lame/files/latest/download/lame.tar.gz
git clone --depth 1 git://anongit.freedesktop.org/xorg/lib/libXext
git clone --depth 1 git://anongit.freedesktop.org/git/xorg/lib/libXfixes
git clone --depth 1 https://github.com/intel/libva
git clone --depth 1 -b libvdpau-1.2 git://people.freedesktop.org/~aplattner/libvdpau
git clone --depth 1 https://chromium.googlesource.com/webm/libvpx
git clone --depth 1 https://github.com/xiph/ogg.git
git clone --depth 1 https://github.com/xiph/opus.git
git clone --depth 1 https://github.com/xiph/theora.git
git clone --depth 1 https://github.com/xiph/vorbis.git
git clone --depth 1 https://code.videolan.org/videolan/x264.git
git clone https://bitbucket.org/multicoreware/x265_git.git
git clone git://anongit.freedesktop.org/git/xorg/proto/xorgproto

CC=clang
CXX=clang++
SRC=/ffmpeg_deps

export FFMPEG_DEPS_PATH=$SRC/libs
mkdir -p $FFMPEG_DEPS_PATH

export PATH="$FFMPEG_DEPS_PATH/bin:$PATH"
export LD_LIBRARY_PATH="$FFMPEG_DEPS_PATH/lib"

cd $SRC
bzip2 -f -d alsa-lib-1.1.0.tar.bz2
tar xf alsa-lib-1.1.0.tar
cd alsa-lib-1.1.0
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static --disable-shared
make clean
make -j$(nproc) all
make install

cd $SRC/drm
# Requires xutils-dev libpciaccess-dev
./autogen.sh
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static
make clean
make -j$(nproc)
make install
export PKG_CONFIG_PATH=$PWD
pkg-config --debug libdrm

cd $SRC/fdk-aac
git checkout a30bfced6b6d6d976c728552d247cb30dd86e238
autoreconf -fiv
CXXFLAGS="$CXXFLAGS" \
./configure --prefix="$FFMPEG_DEPS_PATH" --disable-shared
make clean
make -j$(nproc) all
make install

cd $SRC
tar xzf lame.tar.gz
cd lame-*
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static
make clean
make -j$(nproc)
make install

cd $SRC/libXext
./autogen.sh
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static
make clean
make -j$(nproc)
make install

cd $SRC/xorgproto
./autogen.sh
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static
make clean
make -j$(nproc)
make install

cd $SRC/libXfixes
./autogen.sh
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static
make clean
make -j$(nproc)
make install

cd $SRC/libva
./autogen.sh
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static --disable-shared
make clean
make -j$(nproc) all
make install

cd $SRC/libvdpau
./autogen.sh
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static --disable-shared
make clean
make -j$(nproc) all
make install

cd $SRC/libvpx
LDFLAGS="$CXXFLAGS" ./configure --prefix="$FFMPEG_DEPS_PATH" \
    --disable-examples --disable-unit-tests \
    --size-limit=12288x12288 \
    --extra-cflags="-DVPX_MAX_ALLOCABLE_MEMORY=1073741824"
make clean
make -j$(nproc) all
make install

cd $SRC/ogg
./autogen.sh
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static --disable-crc
make clean
make -j$(nproc)
make install

cd $SRC/opus
./autogen.sh
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static
make clean
make -j$(nproc) all
make install

cd $SRC/theora
# theora requires ogg, need to pass its location to the "configure" script.
CFLAGS="$CFLAGS -fPIC" LDFLAGS="-L$FFMPEG_DEPS_PATH/lib/" \
    CPPFLAGS="$CXXFLAGS -I$FFMPEG_DEPS_PATH/include/" \
    LD_LIBRARY_PATH="$FFMPEG_DEPS_PATH/lib/" \
    ./autogen.sh
./configure --with-ogg="$FFMPEG_DEPS_PATH" --prefix="$FFMPEG_DEPS_PATH" \
    --enable-static --disable-examples
make clean
make -j$(nproc)
make install

cd $SRC/vorbis
./autogen.sh
./configure --prefix="$FFMPEG_DEPS_PATH" --enable-static
make clean
make -j$(nproc)
make install

cd $SRC/x264
LDFLAGS="$CXXFLAGS" ./configure --prefix="$FFMPEG_DEPS_PATH" \
    --enable-static --disable-asm
make clean
make -j$(nproc)
make install

CC=gcc
CXX=g++
cd $SRC/x265_git/build/linux
cmake -G "Unix Makefiles" \
    -DCMAKE_C_COMPILER=$CC -DCMAKE_CXX_COMPILER=$CXX \
    -DCMAKE_C_FLAGS="$CFLAGS" -DCMAKE_CXX_FLAGS="$CXXFLAGS" \
    -DCMAKE_INSTALL_PREFIX="$FFMPEG_DEPS_PATH" -DENABLE_SHARED:bool=off \
    ../../source
make clean
make -j$(nproc) x265-static
make install

# Remove shared libraries to avoid accidental linking against them.
rm $FFMPEG_DEPS_PATH/lib/*.so
rm $FFMPEG_DEPS_PATH/lib/*.so.*
