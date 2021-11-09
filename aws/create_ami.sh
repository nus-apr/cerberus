sudo apt update
sudo apt install -y docker.io
sudo usermod -aG docker ubuntu
sudo apt install -y pypy3 pypy3-dev
sudo pypy3 -m easy_install docker more_itertools
git clone https://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:x-oauth-basic@github.com/rshariffdeen/cerberus