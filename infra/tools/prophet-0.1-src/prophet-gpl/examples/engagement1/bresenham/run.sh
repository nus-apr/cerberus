#!/bin/bash
../../../build/src/prophet run.conf -cpp -consider-all -first-n-loc 200 -feature-para ../../../crawler/para-all.out
cat __fixed_bresenham.cpp
