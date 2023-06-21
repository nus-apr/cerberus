FROM ubuntu:20.04

ENV DEBIAN_FRONTEND=noninteractive
ENV LANG=C.UTF-8

# install required softwares
RUN apt update \
    && apt install -y wget curl git python3 vim unzip bzip2 \
    openjdk-8-jdk maven \
    openssh-client patch software-properties-common time build-essential \
    && rm -rf /var/lib/apt/lists/*

# jdk7 downloaded from https://www.oracle.com/java/technologies/javase/javase7-archive-downloads.html
COPY ./jdk-7u80-linux-x64.tar.gz /tmp/jdk-7u80-linux-x64.tar.gz
RUN tar xvzf /tmp/jdk-7u80-linux-x64.tar.gz -C /usr/lib/jvm/
RUN rm /tmp/jdk-7u80-linux-x64.tar.gz

# set env
ENV JAVA7_HOME /usr/lib/jvm/jdk1.7.0_80
ENV JAVA8_HOME /usr/lib/jvm/java-8-openjdk-amd64
ENV _JAVA_OPTIONS -Djdk.net.URLClassPath.disableClassPathURLCheck=true
ENV JAVA_ARGS -Xmx4g -Xms1g -XX:MaxPermSize=512m
ENV MVN_OPTS -Xmx4g -Xms1g -XX:MaxPermSize=512m
