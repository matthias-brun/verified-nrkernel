
#include<stdint.h>
#include<stdbool.h>
#include<sys/mman.h>

// from the verified code interface!
struct Flags {
    bool is_writable;
    bool is_supervisor;
    bool disable_execute;
};

struct MemRegionExec {
    uint64_t base;
    uint64_t size;
};

struct PageTableEntryExec {
    struct MemRegionExec frame;
    struct Flags flags;
};



typedef uint64_t paddr_t;

int64_t veros_map_frame(uint64_t pml4, uint64_t vaddr, struct PageTableEntryExec *pte);
int64_t veros_unmap_frame(uint64_t pml4, uint64_t vaddr, struct MemRegionExec *ret_frame);


