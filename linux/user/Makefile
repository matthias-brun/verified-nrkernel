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

INCLUDES = -I../include

all: verified_mmap_test malloc_test malloc_test_static

verified_mmap_test: verified_mmap_test.c
	gcc -o $@ -Wall -O3 $(INCLUDES) $<

malloc_test: malloc_test.c libjemalloc.so
	gcc -o $@ -Wall -O3 -g $(INCLUDES) $<

malloc_test_static: malloc_test.c libjemalloc.so
	gcc -o $@ -Wall -O3 -g -no-pie $(INCLUDES) $<  libjemalloc.a

libjemalloc.so: ../jemalloc/Makefile
	(cd ../jemalloc && make)
	cp ../jemalloc/lib/libjemalloc.so .
	cp ../jemalloc/lib/libjemalloc.a .

../jemalloc/Makefile:
	(cd ../jemalloc && EXTRA_CXXFLAGS=-DCONFIG_USE_MMAP_MODULE EXTRA_CFLAGS=-DCONFIG_USE_MMAP_MODULE ./autogen.sh)

clean:
	rm -rf verified_mmap_test
	rm -rf malloc_test
	rm -rf libjemalloc.*

test: verified_mmap_test
	sudo ./verified_mmap_test
