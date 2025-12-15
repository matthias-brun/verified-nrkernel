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

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
#include <stdbool.h>
#include <pthread.h>

#include "velosiraptor/x8664pml4_unit.h"
#include <veros_page_table.h>

extern void *linux_bench_init();
extern int linux_bench_map_one(void *st, unsigned long addr, unsigned long paddr);
extern int linux_bench_unmap_one(void *st, unsigned long addr, unsigned long _paddr);
extern int linux_bench_protect_one(void *st, unsigned long addr, unsigned long _paddr);

extern void *barrelfish_init();
extern int barrelfish_kernel_map_one(void *st, unsigned long addr, unsigned long paddr);
extern int barrelfish_kernel_protect_one(void *st, unsigned long addr, unsigned long paddr);
extern int barrelfish_kernel_unmap_one(void *st, unsigned long addr, unsigned long paddr);

#define PAGE_SIZE 4096
#define BENCHMARK_RUNS 500
#define BENCHMARK_DRYRUNS 5

static unsigned long measurements[BENCHMARK_RUNS+BENCHMARK_DRYRUNS+1];

#define timpespec_diff(t1, t2) ((t2.tv_sec - t1.tv_sec) * 1000000000 + (t2.tv_nsec - t1.tv_nsec))

static pthread_spinlock_t lock;


////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

paddr_t memory_alloc(size_t sz, paddr_t align) {
    return (paddr_t)aligned_alloc(PAGE_SIZE, PAGE_SIZE);
}

void memory_free(paddr_t pa, size_t sz) {
    free((void *)pa);
}

vaddr_t local_phys_to_mem(paddr_t pa) {
    return pa;
}

paddr_t mem_to_local_phys(vaddr_t va) {
    return va;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Verified Page Table Implementation
////////////////////////////////////////////////////////////////////////////////////////////////////


static void *verified_bench_init() {
    char *ptr = (char*) mmap(NULL, PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (ptr == MAP_FAILED) {
      return 0;
    }
    memset(ptr, 0, PAGE_SIZE);
    return ptr;
}

static int verified_map_one(void *st, vaddr_t vaddr, paddr_t paddr) {
    uint64_t flags = 0x3; // readable & writable
    struct PageTableEntryExec pte = {
        .frame = {
            .base = vaddr,
            .size = PAGE_SIZE
        },
        .flags = {
            .is_writable = 1,
            .is_supervisor = 1,
            .disable_execute = 0,
        }
    };
    return veros_map_frame((uint64_t)st, vaddr, &pte);
}

static int verified_unmap_one(void *st, vaddr_t vaddr, paddr_t paddr) {
    struct MemRegionExec frame;
    return veros_unmap_frame((uint64_t)st, vaddr, &frame);
}

static int verified_protect_one(void *st, vaddr_t vaddr, paddr_t paddr) {
    struct PageTableEntryExec pte;
    if (veros_unmap_frame((uint64_t)st, vaddr, &pte.frame)) {
        return 1;
    }
    pte.flags.is_writable = false;
    return veros_map_frame((uint64_t)st, vaddr, &pte);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Velosiraptor Page Table Implementation
////////////////////////////////////////////////////////////////////////////////////////////////////

static int velosiraptor_map_one(void *st, vaddr_t vaddr, paddr_t paddr) {
    pthread_spin_lock(&lock);
    x8664pml4__t *vroot = st;
    flags_t flags = { writable:1, readable: 1};
    size_t r = x8664pml4_map(vroot, vaddr, PAGE_SIZE, flags, paddr);
    pthread_spin_unlock(&lock);
    // printf("Result: %zu\n", r);
    return (r != PAGE_SIZE);
}

static int velosiraptor_protect_one(void *st, vaddr_t vaddr, paddr_t paddr) {
    pthread_spin_lock(&lock);
    x8664pml4__t *vroot = st;
    flags_t flags = { writable:0, readable: 1};
    size_t r =  x8664pml4_protect(vroot, vaddr, PAGE_SIZE, flags);
    pthread_spin_unlock(&lock);
    // printf("Result: %zu\n", r);
    return (r != PAGE_SIZE);
}

static int velosiraptor_unmap_one(void *st, vaddr_t vaddr, paddr_t paddr) {
    pthread_spin_lock(&lock);
    x8664pml4__t *vroot = st;
    size_t r = x8664pml4_unmap(vroot, vaddr, PAGE_SIZE);
    pthread_spin_unlock(&lock);
    // printf("Result: %zu\n", r);
    return (r != PAGE_SIZE);
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Benchmark Driver Function
////////////////////////////////////////////////////////////////////////////////////////////////////

typedef int (*run_fn_t)(void *st, vaddr_t, paddr_t);

static void run_benchmark(const char *label, run_fn_t f, void *st, vaddr_t vaddr, paddr_t paddr) {
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

int main() {
    unsigned long vaddr = 0x0;
    unsigned long paddr = 0x1000;

    pthread_spin_init(&lock, PTHREAD_PROCESS_SHARED);

#ifndef NO_RECLAIM

    // Linux Benchmarks: Full Page Table
    void *linux_st = linux_bench_init();
    assert(linux_st);
    run_benchmark("Linux-x86_64-Map", linux_bench_map_one, linux_st, vaddr, paddr);
    run_benchmark("Linux-x86_64-Protect", linux_bench_protect_one, linux_st, vaddr, paddr);
    run_benchmark("Linux-x86_64-Unmap", linux_bench_unmap_one, linux_st, vaddr, paddr);

    // Velosiraptor Benchmarks: Full Page Table
    x8664pml4__t vroot;
    x8664pml4_alloc(&vroot);
    run_benchmark("Velosiraptor-x86_64-Map", velosiraptor_map_one, &vroot, vaddr, paddr);
    run_benchmark("Velosiraptor-x86_64-Protect", velosiraptor_protect_one,  &vroot, vaddr, paddr);
    run_benchmark("Velosiraptor-x86_64-Unmap", velosiraptor_unmap_one,  &vroot, vaddr, paddr);

    // Verified PT Benchmarks: Full Page Table
    void *verified_state = verified_bench_init();
    assert(verified_state);
    run_benchmark("Verified-x86_64-Map", verified_map_one, verified_state, vaddr, paddr);
    run_benchmark("Verified-x86_64-Protect", verified_protect_one, verified_state, vaddr, paddr);
    run_benchmark("Verified-x86_64-Unmap", verified_unmap_one, verified_state, vaddr, paddr);
#else
    // Verified PT Benchmarks: Full Page Table
    void *verified_state = verified_bench_init();
    assert(verified_state);
    run_benchmark("Verified+NoReclaim-x86_64-Map", verified_map_one, verified_state, vaddr, paddr);
    run_benchmark("Verified+NoReclaim-x86_64-Protect", verified_protect_one, verified_state, vaddr, paddr);
    run_benchmark("Verified+NoReclaim-x86_64-Unmap", verified_unmap_one, verified_state, vaddr, paddr);
#endif /* NO_RECLAIM */
}
