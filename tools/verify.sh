#! /bin/bash

# make sure the path etc is set up correctly
source tools/activate.sh

# display the commands
set -x

# print the verus version
verus --version

# run verus
verus --crate-type=lib --rlimit 250 --cfg feature=\"impl\"  $* page-table/src/lib.rs
