#!/bin/bash

docker run -d -it \
  --name vul4j \
  -v /root/.m2/repository:/root/.m2/repository \
  shark4ce/vul4j