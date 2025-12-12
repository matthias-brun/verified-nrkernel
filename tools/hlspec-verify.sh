#! /bin/bash

# make sure the path etc is set up correctly
source tools/activate.sh

# display the commands
set -x

# print the verus version
verus --version

# run verus
verus --crate-type=lib --rlimit 50 --cfg feature=\"hlspec_user\" --cfg feature=\"impl\"  $* page-table/src/lib.rs
