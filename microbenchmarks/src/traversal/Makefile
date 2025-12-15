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

VERIFIED_PAGE_TABLE_PATH=../../../page-table

CFILES_LINUX=\
	linux-kernel/linux.c \
	linux-kernel/mm/memory.c \
	linux-kernel/mm/pgtable-generic.c \
	linux-kernel/arch/x86/mm/pgtable.c

INC_LINUX=\
	-Ilinux-kernel/include \
	-Ilinux-kernel/arch/x86/include \
	-Ilinux-kernel/arch/x86/include/uapi

CFILES_BARRELFISH=\
	barrelfish-kernel/barrelfish.c

INC_BARRELFISH=\
	-Ibarrelfish-kernel/include

INC_VELOSIRAPTOR=\
	-Ivelosiraptor


INC_VERIFIED=\
	-Iverified
#
CFILES=bench.c $(CFILES_LINUX) $(CFILES_BARRELFISH)
INC=$(INC_LINUX) $(INC_BARRELFISH) $(INC_VELOSIRAPTOR) $(INC_VERIFIED)
ARCHIVES=libpage_table.a
ARCHIVES_NO_RECLAIM=libpage_table_no_reclaim.a

all: bench bench_no_reclaim

bench: $(CFILES) $(ARCHIVES)
	gcc -O3 -o $@ $(INC) $(CFILES) $(ARCHIVES)

bench_no_reclaim: $(CFILES) $(ARCHIVES_NO_RECLAIM)
	gcc -O3 -o $@ $(INC) $(CFILES) $(ARCHIVES_NO_RECLAIM) -DNO_RECLAIM

libpage_table.a:
	(cd $(VERIFIED_PAGE_TABLE_PATH) && RUSTFLAGS=-Awarnings cargo build --features impl --release > /dev/null)
	cp $(VERIFIED_PAGE_TABLE_PATH)/target/release/libpage_table.a $@

libpage_table_no_reclaim.a:
	(cd $(VERIFIED_PAGE_TABLE_PATH) && RUSTFLAGS=-Awarnings cargo build --features noreclaim,impl --release > /dev/null)
	cp $(VERIFIED_PAGE_TABLE_PATH)/target/release/libpage_table.a $@

clean:
	rm -rf bench bench_no_reclaim $(ARCHIVES) $(ARCHIVES_NO_RECLAIM)

run: bench bench_no_reclaim
	./bench
	./bench_no_reclaim