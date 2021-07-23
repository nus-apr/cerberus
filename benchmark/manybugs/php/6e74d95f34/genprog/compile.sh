#!/bin/bash
#
# Generic compilation script for ManyBugs problems, and in fact, most
# "multi-file" problems you might want to deal with in GenProg.
#
# Accepts the path for a target executable of a candidate patch, whose
# directory contains the patched source files for the variant, and applies the
# changes into the source directory for the given problem, before recompiling.
#
# In the event of sanity checking or coverage generation, the directory name
# of the provided executable should be "sanity" or "coverage", respectively,
# although neither of these cases should have any impact upon compilation.
#
# Usage: ./compile.sh __EXE_NAME__
#
here_dir=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )
src_dir="$here_dir"

if [ $# -ne 1 ]; then
  echo "ERROR: no executable name provided"
  exit 1
fi

exe_name=$1
candidate_dir=$(dirname $1)

# Copy all the files across from the candidate directory into the source
# directory for this problem, before re-making the program.
if !(cp $candidate_dir/* $src_dir -rf); then
  echo "ERROR: failed to copy patched files to src directory"
  exit 1
fi

# TODO: may need to handle special cases, such as FBC here
pushd $src_dir
if !(make > /dev/null); then
  echo "ERROR: failed to execute make within problem src directory"
  exit 1
fi
popd