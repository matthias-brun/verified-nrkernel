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

VERIFIED_PAGE_TABLE_PATH=../../page-table

ifeq ($(IMPL),velosiraptor)
	MODULE_NAME=mmap_mod_velosiraptor
	LIBRARY_FILES=
	DEPS=include
	BACKEND=CONFIG_USE_VELOSIRAPTOR
else ifeq ($(IMPL),verified)
	MODULE_NAME=mmap_mod_verified
	LIBRARY_FILES=\
		libpage_table/page_table.o \
		libpage_table.a
	DEPS=$(patsubst libpage_table/%.o, libpage_table/.%.cmd,$(wildcard libpage_table/*.o))
	BACKEND=CONFIG_USE_VERIFIED
else ifeq ($(IMPL),verified_noreclaim)
	MODULE_NAME=mmap_mod_verified_noreclaim
	LIBRARY_FILES=\
		libpage_table_no_reclaim/page_table.o \
		libpage_table_no_reclaim.a
	DEPS=$(patsubst libpage_table_no_reclaim/%.o, libpage_table_no_reclaim/.%.cmd,$(wildcard libpage_table_no_reclaim/*.o))
	BACKEND=CONFIG_USE_VERIFIED_NORECLAIM
endif


EXTRA_CFLAGS=-I../include -Iinclude -Wl,--gc-sections
EXTRA_LDFLAGS += --strip-all

obj-m += $(MODULE_NAME).o
$(MODULE_NAME)-y += verified_mmap_main.o
$(MODULE_NAME)-y += $(LIBRARY_FILES)
$(MODULE_NAME)-objs += $(LIBRARY_FILES)

ccflags-y := -D$(BACKEND) -I../include -Iinclude  -Wl,--gc-sections

#verified_mmap_main.o $(wildcard libpage_table/*.o)

all: $(MODULE_NAME).ko
pre: libpage_table libpage_table_no_reclaim

$(MODULE_NAME).ko: $(DEPS)
ifndef MODULE_NAME
	@echo " Implementation not give. Please set IMPL to {velosiraptor, verified, verified-noreclaim}"
	exit 1
endif
ifeq (, $(DEPS))
	echo "Please run 'make pre' first"
	exit 1
else
	make -C /lib/modules/$(shell uname -r)/build M=$(CURDIR) modules
	cp $(MODULE_NAME).ko mmap_module.ko
endif


clean:
	make -C /lib/modules/$(shell uname -r)/build M=$(CURDIR) clean
	rm -rf mmap_module.ko
	rm -rf libpage_table.a
	rm -rf libpage_table
	rm -rf libpage_table_no_reclaim
	rm -rf libpage_table_no_reclaim.a


libpage_table: libpage_table.a
	mkdir -p libpage_table
	(cd libpage_table && ar x ../libpage_table.a)
	cp libpage_table/page_table-*.page_table.*-cgu.0.rcgu.o libpage_table/page_table.o
	touch libpage_table/.marker

libpage_table_no_reclaim: libpage_table_no_reclaim.a
	mkdir -p libpage_table_no_reclaim
	(cd libpage_table_no_reclaim && ar x ../libpage_table_no_reclaim.a)
	cp libpage_table_no_reclaim/page_table-*.page_table.*-cgu.0.rcgu.o libpage_table_no_reclaim/page_table.o
	touch libpage_table_no_reclaim/.marker

libpage_table/%.cmd:
	touch libpage_table/$*.o.cmd

libpage_table_no_reclaim/%.cmd:
	touch libpage_table_no_reclaim/$*.o.cmd

# Available relocation models:
#     static
#     pic
#     pie
#     dynamic-no-pic
#     ropi
#     rwpi
#     ropi-rwpi
#     default
# RUSTFLAGS="-O -C code-model=kernel -C relocation-model=static -C strip=debuginfo -C opt-level=3 -C debuginfo=0"

libpage_table.a:
	(cd $(VERIFIED_PAGE_TABLE_PATH) && RUSTFLAGS="-Awarnings -O -C code-model=large -C relocation-model=static -C strip=debuginfo -C opt-level=3 -C debuginfo=0" cargo rustc -Zbuild-std  --target x86_64-unknown-none --release --features "linuxmodule impl" > /dev/null)
	cp $(VERIFIED_PAGE_TABLE_PATH)/target/x86_64-unknown-none/release/libpage_table.a $@
	strip --strip-debug -R .llvmcmd -R .llvmbc -R .eh_frame $@
	ranlib $@
	touch .libpage_table.a.cmd

libpage_table_no_reclaim.a:
	(cd $(VERIFIED_PAGE_TABLE_PATH) && RUSTFLAGS="-Awarnings -O -C code-model=large -C relocation-model=static -C strip=debuginfo -C opt-level=3 -C debuginfo=0" cargo rustc -Zbuild-std  --target x86_64-unknown-none --release --features "linuxmodule impl noreclaim" > /dev/null)
	cp $(VERIFIED_PAGE_TABLE_PATH)/target/x86_64-unknown-none/release/libpage_table.a $@
	strip --strip-debug -R .llvmcmd -R .llvmbc -R .eh_frame $@
	ranlib $@
	touch .libpage_table_no_reclaim.a.cmd


install: $(MODULE_NAME).ko
	sudo insmod $(MODULE_NAME).ko

uninstall:
	sudo rmmod $(MODULE_NAME)

update: $(MODULE_NAME).ko
	sudo rmmod $(MODULE_NAME)
	sudo insmod $(MODULE_NAME).ko

