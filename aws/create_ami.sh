sudo apt update
sudo apt install docker.io
sudo usermod -aG docker ubuntu
sudo apt install pypy3 pypy3-dev
pypy3 -m easy_install docker more_itertools
