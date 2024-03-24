#!/bin/bash
apt-get update
DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends  \
  openjdk-11-jdk \
  openjdk-11-jdk-headless \
  ant \
  maven libguice-java