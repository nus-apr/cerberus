FROM ubuntu:18.04
LABEL maintainer="Martin Mirchev <mirchevmartin2203@gmail.com>"

RUN apt-get update && apt-get upgrade -y && apt-get autoremove -y

# install experiment dependencies
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends 