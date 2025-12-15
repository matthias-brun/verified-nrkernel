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

#include <fcntl.h>
#include <sys/ioctl.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>


#include<sys/mman.h>

#include <verified_mmap_ioctl.h>

typedef uint64_t vaddr_t;
typedef uint64_t paddr_t;


#define MY_MMAP_ADDRESS_RANGE_START VA_RANGE_MIN
#define MY_MMAP_ADDRESS_RANGE_END VA_RANGE_MAX
#define MY_MMAP_REGION_SIZE (MY_MMAP_ADDRESS_RANGE_END - MY_MMAP_ADDRESS_RANGE_START + 1)

#define PAGE_SIZE 4096
#define BENCHMARK_RUNS 500
#define BENCHMARK_DRYRUNS 5

static unsigned long measurements[BENCHMARK_RUNS+BENCHMARK_DRYRUNS+1];

#define timpespec_diff(t1, t2) ((t2.tv_sec - t1.tv_sec) * 1000000000 + (t2.tv_nsec - t1.tv_nsec))

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

#include <errno.h>


static int my_mmap(int fd, void *addr, size_t sz, int prot, int flags, int _fd, off_t offset) {
    assert(addr >= (void *)MY_MMAP_ADDRESS_RANGE_START && addr < (void *)MY_MMAP_ADDRESS_RANGE_END);
	union verified_mmap_ioctl_args args;
	args.mmap_args = (struct mmap_args){
		.vaddr = (uint64_t)addr,
		.sz = sz,
		.flags = flags
	};

	if (ioctl(fd, CMD_MMAP, &args) < 0) {
		perror("ioctl mmap failed\n");
		return -1;
	}

    volatile char *ptr = (char *)addr;
    *ptr = 1;

	return 0;
}

static int my_munmap(int fd, void *addr, size_t sz) {
	union verified_mmap_ioctl_args args;
	args.munmap_args = (struct munmap_args){
		.vaddr = (uint64_t)addr,
		.sz = sz
	};

	if (ioctl(fd, CMD_MUNMAP, &args) < 0) {
		perror("ioctl munmap failed\n");
		return -1;
	}
	return 0;
}

static int my_mprotect(int fd, void *addr, size_t sz, int prot) {
	union verified_mmap_ioctl_args args;
	args.mprotect_args = (struct mprotect_args){
		.vaddr = (uint64_t)addr,
		.sz = sz,
		.flags = prot
	};

	if (ioctl(fd, CMD_MPROTECT, &args) < 0) {
		perror("ioctl mprotect failed\n");
        return -1;
	}

    return 0;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Verified Page Table Implementation
////////////////////////////////////////////////////////////////////////////////////////////////////


static int verified_map_one(int st, vaddr_t vaddr, paddr_t paddr) {
    return my_mmap(st, (void *)vaddr, PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0) != 0;
}

static int verified_unmap_one(int st, vaddr_t vaddr, paddr_t paddr) {
    return my_munmap(st, (void *)vaddr, PAGE_SIZE);
}

static int verified_protect_one(int st, vaddr_t vaddr, paddr_t paddr) {
    return my_mprotect(st, (void *)vaddr, PAGE_SIZE, PROT_READ);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Velosiraptor Page Table Implementation
////////////////////////////////////////////////////////////////////////////////////////////////////

static int velosiraptor_map_one(int st, vaddr_t vaddr, paddr_t paddr) {
    return my_mmap(st, (void *)vaddr, PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0) != 0;
}

static int velosiraptor_protect_one(int st, vaddr_t vaddr, paddr_t paddr) {
    return my_munmap(st, (void *)vaddr, PAGE_SIZE);
}

static int velosiraptor_unmap_one(int st, vaddr_t vaddr, paddr_t paddr) {
    return my_mprotect(st, (void *)vaddr, PAGE_SIZE, PROT_READ);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Velosiraptor Page Table Implementation (Single Entry)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Velosiraptor Page Table Implementation (Single Entry)
////////////////////////////////////////////////////////////////////////////////////////////////////

static int linux_map_one(int st, vaddr_t vaddr, paddr_t paddr) {
    int r;

    volatile char *ptr = (char*) mmap((void*)vaddr, PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_POPULATE | MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (ptr == MAP_FAILED) {
      return -1;
    }

    *ptr = 1;
    return 0;
}

static int linux_protect_one(int st, vaddr_t vaddr, paddr_t paddr) {
    return mprotect((void *)vaddr, PAGE_SIZE, PROT_READ);
}

static int linux_unmap_one(int st, vaddr_t vaddr, paddr_t paddr) {
    return munmap((void *)vaddr, PAGE_SIZE);
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Benchmark Driver Function
////////////////////////////////////////////////////////////////////////////////////////////////////

typedef int (*run_fn_t)(int st, vaddr_t, paddr_t);

static void run_benchmark(const char *label, run_fn_t f, int st, vaddr_t vaddr, paddr_t paddr) {
    int r;
    printf("%s: ", label);
    for (int i = 0; i <= BENCHMARK_RUNS + BENCHMARK_DRYRUNS; i++) {
        struct timespec t_start, t_end;
        clock_gettime(CLOCK_MONOTONIC, &t_start);
        r = f(st, vaddr, paddr);
        vaddr += PAGE_SIZE;
        assert(r ==0);
        r = f(st, vaddr, paddr);
        vaddr += PAGE_SIZE;
        assert(r ==0);
        clock_gettime(CLOCK_MONOTONIC, &t_end);

        measurements[i] = timpespec_diff(t_start, t_end) / 2;
        if (i >= BENCHMARK_DRYRUNS) {
            printf("%ld ", measurements[i]);
        }
    }
    printf("\n");
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Benchmark Main
////////////////////////////////////////////////////////////////////////////////////////////////////

#include <pthread.h>
#include <unistd.h>

static volatile bool benchmark_complete = false;

static void *spin_thread(void *arg) {
    while (!benchmark_complete) {
        sched_yield();
    }
    return NULL;
}

int main(int argc, char **argv) {

    unsigned long vaddr = MY_MMAP_ADDRESS_RANGE_START;
    unsigned long paddr = 0x1000;

    // Create spin threads for all cores except one
    int num_cores = sysconf(_SC_NPROCESSORS_ONLN);
    int num_spin_threads = num_cores - 1;
    pthread_t *threads = malloc(num_spin_threads * sizeof(pthread_t));

    for (int i = 1; i < num_spin_threads; i++) {
        pthread_create(&threads[i], NULL, spin_thread, (void *)i);
    }

    sleep(1); // Give threads time to start

    // Linux Benchmarks: Full Page Table
    if (strcmp(argv[1], "linux") == 0) {
        run_benchmark("Linux-x86_64-Map", linux_map_one, 0, vaddr, paddr);
        run_benchmark("Linux-x86_64-Protect", linux_protect_one, 0, vaddr, paddr);
        run_benchmark("Linux-x86_64-Unmap", linux_unmap_one, 0, vaddr, paddr);
    }

    if (strcmp(argv[1], "velosiraptor") == 0) {
        // Velosiraptor Benchmarks: Full Page Table
        int velsoraptor_mmap_fd = open("/proc/verified_mmap", O_RDWR);
        if (velsoraptor_mmap_fd < 0) {
            perror("open");
            return 1;
        }

        void *addr = mmap((void *)MY_MMAP_ADDRESS_RANGE_START, MY_MMAP_REGION_SIZE, PROT_READ | PROT_WRITE, MAP_NORESERVE|MAP_PRIVATE, velsoraptor_mmap_fd, 0);
        if (addr == MAP_FAILED) {
            perror("mmap");
            return 1;
        }
        run_benchmark("Velosiraptor-x86_64-Map", velosiraptor_map_one, velsoraptor_mmap_fd, vaddr, paddr);
        run_benchmark("Velosiraptor-x86_64-Protect", velosiraptor_protect_one,  velsoraptor_mmap_fd, vaddr, paddr);
        run_benchmark("Velosiraptor-x86_64-Unmap", velosiraptor_unmap_one,  velsoraptor_mmap_fd, vaddr, paddr);

    }

    if (strcmp(argv[1], "verified") == 0) {
        // Verified PT Benchmarks: Full Page Table
        int verified_pt_fd = open("/proc/verified_mmap", O_RDWR);
        if (verified_pt_fd < 0) {
            perror("open");
            return 1;
        }

        void *addr = mmap((void *)MY_MMAP_ADDRESS_RANGE_START, MY_MMAP_REGION_SIZE, PROT_READ | PROT_WRITE, MAP_NORESERVE|MAP_PRIVATE, verified_pt_fd, 0);
        if (addr == MAP_FAILED) {
            perror("mmap");
            return 1;
        }

        run_benchmark("Verified-x86_64-Map", verified_map_one, verified_pt_fd, vaddr, paddr);
        run_benchmark("Verified-x86_64-Protect", verified_protect_one, verified_pt_fd, vaddr, paddr);
        run_benchmark("Verified-x86_64-Unmap", verified_unmap_one, verified_pt_fd, vaddr, paddr);
    }

    if (strcmp(argv[1], "verified_noreclaim") == 0) {
        // Verified PT Benchmarks: Full Page Table
        int verified_pt_fd = open("/proc/verified_mmap", O_RDWR);
        if (verified_pt_fd < 0) {
            perror("open");
            return 1;
        }

        void *addr = mmap((void *)MY_MMAP_ADDRESS_RANGE_START, MY_MMAP_REGION_SIZE, PROT_READ | PROT_WRITE, MAP_NORESERVE|MAP_PRIVATE, verified_pt_fd, 0);
        if (addr == MAP_FAILED) {
            perror("mmap");
            return 1;
        }

        run_benchmark("Verified+NoReclaim-x86_64-Map", verified_map_one, verified_pt_fd, vaddr, paddr);
        run_benchmark("Verified+NoReclaim-x86_64-Protect", verified_protect_one, verified_pt_fd, vaddr, paddr);
        run_benchmark("Verified+NoReclaim-x86_64-Unmap", verified_unmap_one, verified_pt_fd, vaddr, paddr);
    }

    benchmark_complete = false;
    for (int i = 1; i < num_spin_threads; i++) {
        void *ret;
        pthread_cancel(threads[i]);
    }
}
