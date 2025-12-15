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

set -e

# the verus repository url
VERUS_REPO="https://github.com/verus-lang/verus.git"

# where to clone the repository into
VERUS_DIR=".verus"

# the verus release to be used
VERUS_RELEASE="release/0.2025.06.14.9b557d7"

# check if verus repo exists, clone it if needed
if [ ! -d .verus ]; then
    git clone $VERUS_REPO $VERUS_DIR
fi

# cd into the verus directory
pushd $VERUS_DIR/source

# update repository
git fetch

# checkout the verus release we want
git checkout $VERUS_RELEASE

# update z3
./tools/get-z3.sh

# activate building
source ../tools/activate       # for bash and zsh

# we need to build for no std
vargo build --release --vstd-no-std --vstd-no-alloc

popd
