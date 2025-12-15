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

CFG_IMPL=verified

build:
	make -C user
	(cd module && IMPL=$(CFG_IMPL) make pre)
	(cd module && IMPL=$(CFG_IMPL) make all)

run:
	make -C user
	(cd module && IMPL=$(CFG_IMPL) make all)
	bash tools/qemu-start.sh $(CFG_IMPL)

clean:
	(cd module && make clean)
	(cd user && make clean)

clean_and_run:
	(cd module && make clean)
	(cd module && IMPL=$(CFG_IMPL) make pre)
	(cd module && IMPL=$(CFG_IMPL) make all)
	(cd user && make clean)
	(cd user && make)
	bash tools/qemu-start.sh $(CFG_IMPL)

test:
	bash tools/test-in-qemu.sh $(CFG_IMPL)

pre:
	bash tools/download-linux-image.sh
	make -C module pre
