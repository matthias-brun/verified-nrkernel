#! /bin/bash

# MIT License
#
# Copyright (c) 2025 Paper #409 Authors, ASPLOS'26.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

# make sure the path etc is set up correctly
source tools/activate.sh

# display the commands
set -x

GIT_HASH=$(git rev-parse --short HEAD)

# run verus with emit dep-info
verus --crate-type=lib --rlimit 50 --cfg feature=\"impl\"  --no-verify --emit=dep-info page-table/src/lib.rs

DEP_FILE=$(pwd)/lib.d
PATCH_FILE=$(pwd)/tools/verus-linecount-fix.patch

pushd ${VERUS_DIR}

echo "Patching bug in linecount tool for verus commit"
git checkout source/tools/line_count/src/main.rs
git apply ${PATCH_FILE}

popd

pushd ${VERUS_DIR}/source/tools/line_count

cargo run --release -- ${DEP_FILE} -p --delimiters-are-layout --proofs-arent-trusted

popd
