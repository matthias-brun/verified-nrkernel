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

#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>

typedef unsigned long lpaddr_t;
typedef unsigned long lvaddr_t;
#define STATIC_ASSERT_SIZEOF(x, y)
#define COUNT(x)
#define NONNULL

#include <offsets_target.h>
#include <paging_target.h>
#include <paging_kernel_target.h>




void *barrelfish_init() {
    return aligned_alloc(BASE_PAGE_SIZE, BASE_PAGE_SIZE);
}

int barrelfish_kernel_map_one(void *st, unsigned long addr, unsigned long paddr) {
    union x86_64_ptable_entry *entry = (union x86_64_ptable_entry *)st + X86_64_PTABLE_BASE(addr);
    paging_x86_64_map(entry, paddr, X86_64_PTABLE_PRESENT | X86_64_PTABLE_READ_WRITE);
    return 0;
}

int barrelfish_kernel_protect_one(void *st, unsigned long addr, unsigned long paddr) {
    union x86_64_ptable_entry *entry = (union x86_64_ptable_entry *)st + X86_64_PTABLE_BASE(addr);
    paging_x86_64_modify_flags(entry, X86_64_PTABLE_PRESENT | X86_64_PTABLE_READ_WRITE | X86_64_PTABLE_EXECUTE_DISABLE);
    return 0;
}


int barrelfish_kernel_unmap_one(void *st, unsigned long addr, unsigned long paddr) {
    union x86_64_ptable_entry *entry = (union x86_64_ptable_entry *)st + X86_64_PTABLE_BASE(addr);
    paging_unmap(entry);
    return 0;
}