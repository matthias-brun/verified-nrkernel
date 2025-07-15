#! /bin/bash

# make sure the path etc is set up correctly
source tools/activate.sh

# display the commands
set -x

# run verus
verus --crate-type=lib  --rlimit 50 $* page-table/src/lib.rs