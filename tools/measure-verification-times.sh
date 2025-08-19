#! /bin/bash

# make sure the path etc is set up correctly
source tools/activate.sh

# display the commands
set -x

GIT_HASH=$(git rev-parse --short HEAD)

# run verus
verus --crate-type=lib  \
      --rlimit 50 \
      --cfg feature=\"impl\" \
      --no-auto-recommends-check \
      --time-expanded \
      --output-json \
      --num-threads 32 \
    page-table/src/lib.rs > "verification-times-${GIT_HASH}.json"
