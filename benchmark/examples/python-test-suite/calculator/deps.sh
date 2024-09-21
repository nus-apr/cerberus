#!/bin/bash
apt-get update
DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends  \
  python3-pip
pip3 install pytest pytest-timeout