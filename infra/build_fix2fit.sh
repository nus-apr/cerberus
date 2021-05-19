#!/bin/bash

git clone https://github.com/gaoxiang9430/Fix2Fit.git
cd Fix2Fit
git submodule update --init --recursive

./infra/base-images/all.sh
