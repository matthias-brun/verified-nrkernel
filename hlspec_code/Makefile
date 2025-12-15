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

all: map_unmap_fault threads_4 two_threads_map

run: all mmap_mod_verified.ko
	@echo "\nInstalling module"
	sudo insmod mmap_mod_verified.ko
	@echo "\nRunning two_threads_map:"
	./two_threads_map
	@echo "\nRunning threads_4:"
	./threads_4
	@echo "\nRunning map_unmap_fault (expecting segfault, may take a little while.)"
	./map_unmap_fault || true
	@echo "\nUnloading module."
	sudo rmmod mmap_mod_verified.ko
	@echo "Done."




map_unmap_fault: franken_programs/map_unmap_fault.c
	gcc $(CFLAGS) -o $@ $<

threads_4: franken_programs/threads_4.c
	gcc $(CFLAGS) -o $@ $<

two_threads_map: franken_programs/two_threads_map.c
	gcc $(CFLAGS) -o $@ $<

mmap_mod_verified.ko:
	IMPL=verified $(MAKE) -C ../linux/module
	cp ../linux/module/mmap_mod_verified.ko $@