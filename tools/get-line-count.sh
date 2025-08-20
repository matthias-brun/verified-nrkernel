#! /bin/bash

# make sure the path etc is set up correctly
source tools/activate.sh

# display the commands
set -x

GIT_HASH=$(git rev-parse --short HEAD)

# run verus with emit dep-info
verus --crate-type=lib --rlimit 50 --cfg feature=\"impl\"  --no-verify --emit=dep-info page-table/src/lib.rs

DEP_FILE=$(pwd)/lib.d

pushd ${VERUS_DIR}/source/tools/line_count

cargo run --release -- ${DEP_FILE} -p --delimiters-are-layout --proofs-arent-trusted

popd
