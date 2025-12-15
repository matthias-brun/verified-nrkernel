// MIT License
//
// Copyright (c) 2025 Paper #409 Authors, ASPLOS'26.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#include <sys/ioctl.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <string.h>
#include <sys/mman.h>

#include <verified_mmap_ioctl.h>


#define MY_MMAP_ADDRESS_RANGE_START VA_RANGE_MIN
#define MY_MMAP_ADDRESS_RANGE_END VA_RANGE_MAX
#define MY_MMAP_REGION_SIZE (MY_MMAP_ADDRESS_RANGE_END - MY_MMAP_ADDRESS_RANGE_START + 1)

#define LARGE_PAGE_SIZE (1ULL << 21)
#define BASE_PAGE_SIZE (1ULL << 12)

static int my_mmap_fd = -1;

static int open_mmap_fd(void) {
	my_mmap_fd = open("/proc/verified_mmap", O_RDWR);
	if (my_mmap_fd < 0) {
		perror("open");
		return 1;
	}

	// PROT_NONE is commonly employed for "guard" pages at the end of stacks.
	// void *addr = mmap((void *)MY_MMAP_ADDRESS_RANGE_START, MY_MMAP_REGION_SIZE, PROT_NONE, MAP_NORESERVE|MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
	printf("Calling mmap with fd=%d\n", my_mmap_fd);
	void *addr = mmap((void *)MY_MMAP_ADDRESS_RANGE_START, MY_MMAP_REGION_SIZE, PROT_READ | PROT_WRITE, MAP_NORESERVE|MAP_PRIVATE, my_mmap_fd, 0);
	if (addr == MAP_FAILED) {
		perror("mmap");
		return 1;
	}

	return 0;
}

static int close_mmap_fd(void) {
    return close(my_mmap_fd);
}

static void *my_mmap(void *addr, size_t sz, int prot, int flags, int fd, off_t offset) {
    assert(addr >= (void *)MY_MMAP_ADDRESS_RANGE_START && addr < (void *)MY_MMAP_ADDRESS_RANGE_END);
	union verified_mmap_ioctl_args args;
	args.mmap_args = (struct mmap_args){
		.vaddr = (uint64_t)addr,
		.sz = sz,
		.flags = flags
	};

	if (ioctl(my_mmap_fd, CMD_MMAP, &args) < 0) {
		perror("ioctl mmap failed\n");
		return MAP_FAILED;
	}
	return addr;
}

static int my_munmap(void *addr, size_t sz) {
	union verified_mmap_ioctl_args args;
	args.munmap_args = (struct munmap_args){
		.vaddr = (uint64_t)addr,
		.sz = sz
	};

	if (ioctl(my_mmap_fd, CMD_MUNMAP, &args) < 0) {
		perror("ioctl munmap failed\n");
		return -1;
	}
	return 0;
}

static void my_mprotect(void *addr, size_t sz, int prot) {
	union verified_mmap_ioctl_args args;
	args.mprotect_args = (struct mprotect_args){
		.vaddr = (uint64_t)addr,
		.sz = sz,
		.flags = prot
	};

	if (ioctl(my_mmap_fd, CMD_MPROTECT, &args) < 0) {
		perror("ioctl mprotect failed\n");
	}
}

int main (int argc, char **argv)
{
    uint64_t *value;
    void *addr;

    if (open_mmap_fd()) {
        printf("failed to initialize the mmap subsystem\n");
        return -1;
    }


    printf("mapping memory...\n");
    addr = my_mmap((void *)MY_MMAP_ADDRESS_RANGE_START, BASE_PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_ANONYMOUS, -1, 0);
    if (addr == MAP_FAILED) {
        perror("mmap");
        return 1;
    }

    value = (uint64_t *)addr;
    printf("accessing memory...\n");
	printf("Value is =%lx\n", *value);
	printf("writing memory...\n");
    *value = 0x12345678;


    printf("changing permissions\n");
    my_mprotect(addr, BASE_PAGE_SIZE, PROT_READ);
    printf("accessing memory...\n");
    printf("Value is =%lx\n", *value);

    printf("unmapping...\n");
    my_munmap(addr, BASE_PAGE_SIZE);
    printf("done.\n");


	printf("Mmapping (huge)...\n");
    addr = my_mmap((void *)MY_MMAP_ADDRESS_RANGE_START + LARGE_PAGE_SIZE, LARGE_PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_ANONYMOUS, -1, 0);
    if (addr == MAP_FAILED) {
        perror("mmap");
        return 1;
    }

    value = (uint64_t *)addr;
    printf("accessing memory...\n");
    value[0] = 0x12345678;
    value[1024] = 0x12345678;


    printf("changing permissions\n");
    my_mprotect(addr, LARGE_PAGE_SIZE, PROT_READ);
    printf("accessing memory...\n");
    printf("Value is =%lx\n", *value);

    printf("unmapping...\n");
    my_munmap(addr, LARGE_PAGE_SIZE);
    printf("done.\n");


    close_mmap_fd();
    return 0;
}


