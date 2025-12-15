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

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)

# where to clone the repository into
VERUS_DIR="${REPOSITORY_ROOT}/.verus"

OPEN=

for i in "$@"; do
  case $i in
    --open)
      OPEN=--open
      shift
      ;;
    -*|--*)
      echo "Unknown option $i"
      exit 1
      ;;
    *)
      ;;
  esac
done

# check if verus repo exists, clone it if needed
if [ ! -d "${VERUS_DIR}" ]; then
    "${REPOSITORY_ROOT}"/tools/update-verus.sh
fi

if [ `uname` == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ `uname` == "Linux" ]; then
    DYN_LIB_EXT=so
else
    echo "unsupported OS"
    exit 1
fi


# disable the default rustdoc generation
# pushd "${REPOSITORY_ROOT}/allocator"
# cargo doc --no-deps --document-private-items
# popd

source ${VERUS_DIR}/tools/activate

pushd ${VERUS_DIR}/source

if [ ! -f ${VERUS_DIR}/source/target/debug/verusdoc ]; then
  echo "Building verusdoc..."
  vargo build -p verusdoc
fi

if [ ! -f ${VERUS_DIR}/source/target-verus/debug/libvstd.rlib ]; then
  echo "Building vstd..."
  vargo build --vstd-no-verify
fi

popd

echo "Running rustdoc..."
RUSTC_BOOTSTRAP=1 eval ""VERUSDOC=1 VERUS_Z3_PATH="$(pwd)/z3" rustdoc \
  --extern builtin=${VERUS_DIR}/source/target-verus/debug/libbuiltin.rlib \
  --extern builtin_macros=${VERUS_DIR}/source/target-verus/debug/libbuiltin_macros.$DYN_LIB_EXT \
  --extern state_machines_macros=${VERUS_DIR}/source/target-verus/debug/libstate_machines_macros.$DYN_LIB_EXT \
  --extern vstd=${VERUS_DIR}/source/target-verus/debug/libvstd.rlib \
  --edition=2021 \
  --cfg verus_keep_ghost \
  --cfg verus_keep_ghost_body \
  --cfg 'feature=\"impl\"' \
  --document-private-items \
  -Zcrate-attr=feature\\\(stmt_expr_attributes\\\) \
  -Zcrate-attr=feature\\\(negative_impls\\\) \
  -Zcrate-attr=feature\\\(register_tool\\\) \
  -Zcrate-attr=feature\\\(rustc_attrs\\\) \
  -Zcrate-attr=feature\\\(unboxed_closures\\\) \
  -Zcrate-attr=register_tool\\\(verus\\\) \
  -Zcrate-attr=register_tool\\\(verifier\\\) \
  -Zcrate-attr=register_tool\\\(verusfmt\\\) \
  -Zcrate-attr=allow\\\(internal_features\\\) \
  -Zcrate-attr=allow\\\(unused_braces\\\) \
  -Zproc-macro-backtrace \
  ${REPOSITORY_ROOT}/page-table/src/lib.rs""


echo "Running post-processor..."
${VERUS_DIR}/source/target/debug/verusdoc --help

if [ "$OPEN" = '--open' ]; then
  echo "Opening documentation..."
  open "${REPOSITORY_ROOT}"/doc/lib/index.html
fi

