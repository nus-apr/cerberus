#!/bin/bash
echo "Removing output, logs, results and experiments"
rm -rf output
rm -rf logs
rm -rf results
rm -rf experiments

# if composite_workspace exists, remove it
if [ -d "composite_workspace" ]; then
  echo "Removing composite_workspace"
  sudo rm -rf composite_workspace
fi
