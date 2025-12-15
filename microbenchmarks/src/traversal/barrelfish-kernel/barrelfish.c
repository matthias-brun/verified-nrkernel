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