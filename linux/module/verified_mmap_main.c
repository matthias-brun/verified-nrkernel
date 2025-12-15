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

#include <asm-generic/memory_model.h>
#include <asm/pgalloc.h>
#include <asm/tlbflush.h>
#include <linux/fs.h>
#include <linux/init.h>
#include <linux/kallsyms.h>
#include <linux/kprobes.h>
#include <linux/mm.h>
#include <linux/module.h>
#include <linux/proc_fs.h>
#include <linux/uaccess.h>
#include <linux/cpumask.h>

#include "../include/verified_mmap_ioctl.h"

/// switch to enable the Velosiraptor code, instead of the Rust module
// #define CONFIG_USE_VELOSIRAPTOR

/// the proc file name
static struct proc_dir_entry* proc_entry = NULL;

#define BASE_PAGE_SIZE (1ULL << 12)
#define LARGE_PAGE_SIZE (1ULL << 21)

#ifndef HPAGE_SHIFT
#define HPAGE_SHIFT 21
#endif

////////////////////////////////////////////////////////////////////////////////////////////////////
// Kernel functionality that should be accessible
////////////////////////////////////////////////////////////////////////////////////////////////////
#ifdef CONFIG_HIGHPTE
#define PGTABLE_HIGHMEM __GFP_HIGHMEM
#else
#define PGTABLE_HIGHMEM 0
#endif

/// we don't know about this one!
struct mm_struct init_mm;

// void print(const char* str, unsigned long val);
// void print(const char* str, unsigned long val)
// {
//     printk(KERN_INFO "Verified-MMAP: %s %lx (%lu)\n", str, val, val);
// }

////////////////////////////////////////////////////////////////////////////////////////////////////
// Allowing TLB flushes from a module!
////////////////////////////////////////////////////////////////////////////////////////////////////

void (*flush_tlb_mm_range_func)(struct mm_struct*, unsigned long, unsigned long, unsigned int, bool);

static inline void flush_tlb_mm_range(struct mm_struct* mm, unsigned long start,
    unsigned long end, unsigned int stride_shift,
    bool freed_tables)
{
    if (flush_tlb_mm_range_func) {
        flush_tlb_mm_range_func(mm, start, end, stride_shift, freed_tables);
    } else {
        pr_alert("warning. flush_tlb_mm_range_func not set. Just emitting invlpg not doing shootdown");
        asm volatile("invlpg (%0)" ::"r"(start) : "memory");
    }
}

void flush_tlb_mm_page(struct mm_struct *mm, unsigned long start, unsigned long page_size);
void flush_tlb_mm_page(struct mm_struct *mm, unsigned long start, unsigned long page_size) {

    // finally flush the TLB range
    flush_tlb_mm_range(mm, start, start + page_size, page_size == PAGE_SIZE ? PAGE_SHIFT : HPAGE_SHIFT, true);
}

/// entry point from verified rust code
void flush_tlb_page(unsigned long start, unsigned long page_size);
void flush_tlb_page(unsigned long start, unsigned long page_size) {
    struct mm_struct* mm = current->mm;
    flush_tlb_mm_page(mm, start, page_size);
}

#define KPROBE_KALLSYMS_LOOKUP 1
typedef unsigned long (*kallsyms_lookup_name_t)(const char* name);

// find the address of the TLB flush symbol, so we can invalidate the TLB
static int find_tlb_invalidate_symbol(void)
{

    struct kprobe kp = {
        .symbol_name = "kallsyms_lookup_name"
    };

    // look up the address of the kallsyms_lookup_name function
    register_kprobe(&kp);
    kallsyms_lookup_name_t kallsyms_lookup_name = (kallsyms_lookup_name_t)kp.addr;
    unregister_kprobe(&kp);

    if (!unlikely(kallsyms_lookup_name)) {
        pr_alert("Could not retrieve kallsyms_lookup_name address\n");
        printk(KERN_INFO "Verified MMAP: Could not retrieve kallsyms_lookup_name address\n");
        return -ENXIO;
    }

    // now lookup the function symbol address
    flush_tlb_mm_range_func = (void*)kallsyms_lookup_name("flush_tlb_mm_range");
    if (!unlikely(flush_tlb_mm_range_func)) {
        printk(KERN_INFO "Verified MMAP: Could not retrieve flush_tlb_mm_range function\n");
        return -ENXIO;
    }

    return 0;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// CPU Stuff
////////////////////////////////////////////////////////////////////////////////////////////////////

unsigned int get_current_cpu_id(void);
unsigned int get_current_cpu_id(void)
{
    return smp_processor_id();
}

unsigned int get_num_cpus(void);
unsigned int get_num_cpus(void)
{
    return num_online_cpus();
}

void do_cpu_relax(void);
void do_cpu_relax(void)
{
    cpu_relax();
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Page Table Locks
////////////////////////////////////////////////////////////////////////////////////////////////////

void mmap_mm_pgtable_lock(struct mm_struct *mm);
void mmap_mm_pgtable_lock(struct mm_struct *mm) {
    spin_lock(&mm->page_table_lock);
}

void mmap_pgtable_lock(void);
void mmap_pgtable_lock(void) {
    mmap_mm_pgtable_lock(current->mm);
}

void mmap_mm_pgtable_unlock(struct mm_struct *mm);
void mmap_mm_pgtable_unlock(struct mm_struct *mm) {
    spin_unlock(&mm->page_table_lock);
}

void mmap_pgtable_unlock(void);
void mmap_pgtable_unlock(void) {
    mmap_mm_pgtable_unlock(current->mm);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Converting between Physical and Kernel Virtual Addresses
////////////////////////////////////////////////////////////////////////////////////////////////////

uint64_t local_phys_to_mem(uint64_t pa);
uint64_t local_phys_to_mem(uint64_t pa)
{
    // printk(KERN_INFO "Verified MMAP: pa:%llx -> va:%llx\n\n\n", pa, __va(pa));
    return (uint64_t)__va(pa);
}

uint64_t mem_to_local_phys(uint64_t va);
uint64_t mem_to_local_phys(uint64_t va)
{
    return __pa(va);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Allocating and Deallocating Memory
////////////////////////////////////////////////////////////////////////////////////////////////////

gfp_t __userpte_alloc_gfp = GFP_PGTABLE_USER | PGTABLE_HIGHMEM;

pgtable_t pte_alloc_one(struct mm_struct* mm)
{
    return __pte_alloc_one(mm, __userpte_alloc_gfp);
}

/// allocates memory for the page table
static uint64_t do_alloc_pt_memory(size_t sz, uint64_t align, uint8_t level)
{
    BUG_ON(align != sz);
    BUG_ON(sz != 4096);

    // printk(KERN_INFO "Verified MMAP: alloc pt memory %d\n\n\n", level);

    struct mm_struct* mm = current->mm;
    unsigned long address = 0; // doesn't seem to be needed

    unsigned long ptaddr;
    // char* ty;

    switch (level) {
    case 1: {
        pgtable_t new = pte_alloc_one(mm);
        ptaddr = new ? page_to_pfn(new) << PAGE_SHIFT : 0;
        // ty = "PTable";
        mm_inc_nr_ptes(mm); // increase bookkeeping
        break;
    }
    case 2: {
        pmd_t* new = pmd_alloc_one(mm, address);
        ptaddr = new ? __pa(new) : 0;
        // ty = "PDIR";
        mm_inc_nr_pmds(mm); // increase bookkeeping
        break;
    }
    case 3: {
        pud_t* new = pud_alloc_one(mm, address);
        ptaddr = new ? __pa(new) : 0;
        // ty = "PDPT";
        mm_inc_nr_puds(mm); // increase bookkeeping
        break;
    }
    case 4: {
        printk(KERN_ERR "tried to allocate PML4?\n");
        // BUG();
        // pgd_t *new = pgd_alloc(mm);
        // ptaddr = new ? __pa(new) : 0;
        // fallthrough
        return 0;
    }
    default:
        return 0;
    }

    // printk(KERN_INFO "Verified MMAP: ptmemory allocated %s %016lx\n\n\n", ty, ptaddr);

    return ptaddr;
}

/// frees a page used for a page table
static void do_free_pt_memory(uint64_t addr, size_t sz, uint8_t level)
{
    struct mm_struct* mm = current->mm;

    // printk(KERN_INFO "Verified MMAP: free pt %d %016lx\n", level, addr);

    switch (level) {
    case 1:
        pte_free(mm, pfn_to_page(addr >> PAGE_SHIFT));
        mm_dec_nr_ptes(mm); // increase bookkeeping
        break;
    case 2:
        pmd_free(mm, __va(addr));
        mm_dec_nr_pmds(mm); // increase bookkeeping
        break;
    case 3:
        pud_free(mm, __va(addr));
        mm_dec_nr_puds(mm); // increase bookkeeping
        break;
    default:
        break;
    }
}

uint64_t alloc_frame(size_t sz);
uint64_t alloc_frame(size_t sz)
{
    int order = 0;
    if (sz == LARGE_PAGE_SIZE) {
        order = 9;
    }

    struct page* page = alloc_pages(GFP_USER | __GFP_ZERO, order);

    // shall we pin this page?

    if (page) {
        // get_page(page);
        return PFN_PHYS(page_to_pfn(page));
    } else {
        return 0;
    }
}

void free_frame(uint64_t frame, size_t sz);
void free_frame(uint64_t frame, size_t sz)
{
    int order = 0;
    if (sz == LARGE_PAGE_SIZE) {
        order = 9;
    }

    // unpin the user page
    // unpin_user_page(pfn_to_page(frame >> PAGE_SHIFT))

    free_pages((uint64_t)__va(frame), order);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// end of kernel functionality that should be accessible...
////////////////////////////////////////////////////////////////////////////////////////////////////

#ifdef CONFIG_USE_VELOSIRAPTOR

#define assert(x) BUG_ON(!(x))

#include "include/velosiraptor/myos.h"
#include "include/velosiraptor/types.h"
#include "include/velosiraptor/x8664pagetable_unit.h"
#include "include/velosiraptor/x8664pdir_unit.h"
#include "include/velosiraptor/x8664pdpt_unit.h"
#include "include/velosiraptor/x8664pml4_unit.h"

/// converts the mmap flags to the internal flags used by the code
static inline flags_t convert_flags(uint64_t flags)
{
    flags_t flgs = { .readable = 1, .writable = 1, .usermode = 1 };
    return flgs;
}

/// allocates memory for the page table
uint64_t pt_memory_alloc(size_t sz, paddr_t align, UnitType level)
{
    BUG_ON(align != sz);
    BUG_ON(sz != 4096);

    switch (level) {
    case UnitType_X8664PageTable:
        return do_alloc_pt_memory(sz, align, 1);
    case UnitType_X8664PDir:
        return do_alloc_pt_memory(sz, align, 2);
    case UnitType_X8664PDPT:
        return do_alloc_pt_memory(sz, align, 3);
    case UnitType_X8664PML4:
        return do_alloc_pt_memory(sz, align, 4);
    default:
        return 0;
    }
}

/// frees memory for the page table
void pt_memory_free(paddr_t pa, size_t sz, UnitType level)
{
    switch (level) {
    case UnitType_X8664PageTable:
        return do_free_pt_memory(pa, sz, 1);
    case UnitType_X8664PDir:
        return do_free_pt_memory(pa, sz, 2);
    case UnitType_X8664PDPT:
        return do_free_pt_memory(pa, sz, 3);
    case UnitType_X8664PML4:
        return do_free_pt_memory(pa, sz, 4);
    default:
        return;
    }
}

#else

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

void rust_eh_personality(void);
void rust_eh_personality(void) {
    // do nothing
}


typedef uint64_t paddr_t;

// void pt_memory_free(paddr_t pa, size_t sz);
// uint64_t pt_memory_alloc(size_t sz, paddr_t align, uint8_t level);

// the handlers for the page table operations
extern int64_t veros_init(void);
int64_t veros_map_frame(uint64_t pml4, uint64_t vaddr, struct PageTableEntryExec *pte);
int64_t veros_unmap_frame(uint64_t pml4, uint64_t vaddr, struct MemRegionExec *ret_frame);


/// allocates memory for the page table
uint64_t pt_memory_alloc(size_t sz, paddr_t align, uint8_t level);
uint64_t pt_memory_alloc(size_t sz, paddr_t align, uint8_t level)
{
    BUG_ON(align != sz);
    BUG_ON(sz != 4096);
    // levels: 0 -> allocate ppdt, 1 -> allocate pdir, 2 -> allocate ptable
    return do_alloc_pt_memory(sz, align, 3 - level);
}

/// frees memory for the page table
void pt_memory_free(paddr_t pa, size_t sz, uint8_t level);
void pt_memory_free(paddr_t pa, size_t sz, uint8_t level)
{
    BUG_ON(sz != 4096);
    // levels: 0 -> allocate ppdt, 1 -> allocate pdir, 2 -> allocate ptable
    return do_free_pt_memory(pa, sz, 3 - level);
}

#endif

////////////////////////////////////////////////////////////////////////////////////////////////////
// support functions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// validates whether the range is within the allowed range
/// TODO: check this with the corresponding VMA region
static int validate_range(struct vm_area_struct* vma, uint64_t vaddr, uint64_t sz)
{
    if (vaddr < VA_RANGE_MIN || vaddr + sz > VA_RANGE_MAX) {
        printk(KERN_INFO "Verified MMAP: invalid range\n");
        // return 1;
    }

    // we only support single page mappings
    if (sz != BASE_PAGE_SIZE && sz != LARGE_PAGE_SIZE) {
        printk(KERN_INFO "Verified MMAP: invalid size\n");
        return 1;
    }

    // the address must be aligned with the size
    if ((vaddr & (sz - 1)) != 0) {
        printk(KERN_INFO "Verified MMAP: unaligned address\n");
        return 1;
    }

    return 0;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Wrappers that call into the verified mmap implementation
////////////////////////////////////////////////////////////////////////////////////////////////////

#ifdef CONFIG_USE_VELOSIRAPTOR

static int do_map_page(struct mm_struct *mm, pgd_t* pgd, uint64_t vaddr, uint64_t sz, uint64_t flags)
{
    int ret = 0;

    // initialize the pointer to the page table
    x8664pml4__t pml4;
    x8664pml4_init(&pml4, __pa(pgd));

    uint64_t frame = alloc_frame(sz);
    if (frame == 0) {
        return -ENOMEM;
    }

    mmap_mm_pgtable_lock(mm);

    flags_t flgs = convert_flags(flags);
    if (x8664pml4_map(&pml4, vaddr, sz, flgs, frame) != sz) {
        printk(KERN_INFO "Verified MMAP: mmap   failed.\n");
        free_frame(frame, sz);
        ret = -ENOMEM;
    }

    mmap_mm_pgtable_unlock(mm);

    return ret;
}

static int do_protect_page(struct mm_struct *mm, pgd_t* pgd, uint64_t vaddr, uint64_t sz, uint64_t flags)
{
    int res = 0;

    // initialize the pointer to the page table
    x8664pml4__t pml4;
    x8664pml4_init(&pml4, __pa(pgd));

    mmap_mm_pgtable_lock(mm);

    flags_t flgs = convert_flags(flags);
    if (x8664pml4_protect(&pml4, vaddr, sz, flgs) != sz) {
        printk(KERN_INFO "Verified MMAP: do_verified_mprotect   failed.\n");
        res = -ENOMEM;
    }

    mmap_mm_pgtable_unlock(mm);

    // finally flush the TLB range
    flush_tlb_mm_range(mm, vaddr, vaddr + sz, sz == PAGE_SIZE ? PAGE_SHIFT : HPAGE_SHIFT, false);

    return res;
}

static int do_unmap_page(struct mm_struct *mm, pgd_t* pgd, uint64_t vaddr, uint64_t sz)
{
    // initialize the pointer to the page table
    x8664pml4__t pml4;
    x8664pml4_init(&pml4, __pa(pgd));

    mmap_mm_pgtable_lock(mm);

    uint64_t paddr = 0;
    if (!x8664pml4_resolve(&pml4, vaddr, &paddr)) {
        printk(KERN_INFO "Verified MMAP: do_verified_munmap   was not mapped.\n");
        mmap_mm_pgtable_lock(mm);
        return 0; // we return ok here.
    }

    if (x8664pml4_unmap(&pml4, vaddr, sz) != sz) {
        printk(KERN_INFO "Verified MMAP: do_verified_munmap   failed.\n");
        mmap_mm_pgtable_unlock(mm);
        return -ENOMEM;
    }

    mmap_mm_pgtable_unlock(mm);

    flush_tlb_mm_range(mm, vaddr, vaddr + sz, sz == PAGE_SIZE ? PAGE_SHIFT : HPAGE_SHIFT, false);

    free_frame(paddr, sz);

    return 0;
}

#else // !CONFIG_USE_VELOSIRAPTOR

static int do_map_page(struct mm_struct *mm, pgd_t* pgd, uint64_t vaddr, uint64_t sz, uint64_t flags)
{
    uint64_t pml4 = __pa(pgd);

    uint64_t frame = alloc_frame(sz);
    if (frame == 0) {
        return -ENOMEM;
    }

    struct PageTableEntryExec pte = {
        .frame = {
            .base = frame,
            .size = sz
        },
        .flags = {
            .is_writable = 1,
            .is_supervisor = 0,
            .disable_execute = 1,
        }
    };

    // printk(KERN_INFO "Verified MMAP: map   mm=%p, va=%016llx pa=%016llx", mm, vaddr, frame);

    // mmap_mm_pgtable_lock(mm); lock taken in verified code
    int res = veros_map_frame(pml4, vaddr, &pte);
    // mmap_mm_pgtable_unlock(mm); lock taken in verified code

    if (res != 0) {
        free_frame(frame, sz);
        return -EINVAL;
    }

    return 0;
}

static int do_protect_page(struct mm_struct *mm, pgd_t* pgd, uint64_t vaddr, uint64_t sz, uint64_t flags)
{
    uint64_t pml4 = __pa(pgd);

    struct MemRegionExec frame = {
        .base = 0,
        .size = 0
    };

    // printk(KERN_INFO "Verified MMAP: protect   mm=%p, va=%016llx pa=%016llx", mm, vaddr);

    // mmap_mm_pgtable_lock(mm); lock taken in verified code
    int res = veros_unmap_frame(pml4, vaddr, &frame);
    if (res != 0) {
        return -EINVAL;
    }

    struct PageTableEntryExec pte = {
        .frame = frame,
        .flags = {
            .is_writable = 1,
            .is_supervisor = 0,
            .disable_execute = 1,
        }
    };

    res = veros_map_frame(pml4, vaddr, &pte);
    if (res != 0) {
        return -EINVAL;
    }

    return 0;
}

static int do_unmap_page(struct mm_struct *mm, pgd_t* pgd, uint64_t vaddr, uint64_t sz)
{
    uint64_t pml4 = __pa(pgd);

    struct MemRegionExec frame = {
        .base = 0,
        .size = 0
    };

    // mmap_mm_pgtable_lock(mm); lock taken in verified code
    int res = veros_unmap_frame(pml4, vaddr, &frame);
    // mmap_mm_pgtable_unlock(mm); lock taken in verified code

    if (res != 0) {
        return -EINVAL;
    }

    // printk(KERN_INFO "Verified MMAP: unmapped   mm=%p, va=%016llx pa=%016llx", mm, vaddr, frame.base);

    free_frame(frame.base, frame.size);

    return 0;
}

#endif // CONFIG_USE_VELOSIRAPTOR

////////////////////////////////////////////////////////////////////////////////////////////////////
// Handlers of the MMAP/MPROTECT/MUNMAP operations
////////////////////////////////////////////////////////////////////////////////////////////////////

static int do_verified_mmap(struct mm_struct* mm, uint64_t vaddr, uint64_t sz, uint64_t flags)
{
    int res = 0;
    struct vm_area_struct* vma = NULL;

    // printk(KERN_INFO "Verified MMAP: do_verified_mmap   mm=%p, va=%016llx..%016llx\n, flags=%llx", mm, vaddr, vaddr + sz - 1, flags);

    // get the VMA struct
    vma = find_vma(mm, vaddr);
    if (!vma) {
        printk(KERN_INFO "Verified MMAP: do_verified_mmap   no VMA found.\n");
        return -EINVAL;
    }

    if (validate_range(vma, vaddr, sz)) {
        return -EINVAL;
    }

    // only works without PTI, otherwise kernel_to_user_pgdp(mm->pgd) is needed
    res = do_map_page(mm, mm->pgd, vaddr, sz, flags);
    if (res != 0) {
        return res;
    }

    return res;
}

static int do_verified_mprotect(struct mm_struct* mm, uint64_t vaddr, uint64_t sz, uint64_t flags)
{
    int res = 0;
    struct vm_area_struct* vma = NULL;

    // printk(KERN_INFO "Verified MMAP: do_verified_mprotect   mm=%p, va=%016llx..%016llx\n, flags=%llx", mm, vaddr, vaddr + sz - 1, flags);

    // get the VMA struct
    vma = find_vma(mm, vaddr);
    if (!vma) {
        printk(KERN_INFO "Verified MMAP: do_verified_mmap   no VMA found.\n");
        return -EINVAL;
    }

    if (validate_range(vma, vaddr, sz)) {
        return -EINVAL;
    }

    // only works without PTI, otherwise kernel_to_user_pgdp(mm->pgd) is needed
    res = do_protect_page(mm, mm->pgd, vaddr, sz, flags);
    if (res != 0) {
        return res;
    }

    return res;
}

static int do_verified_munmap(struct mm_struct* mm, uint64_t vaddr, uint64_t sz)
{
    int res = 0;

    struct vm_area_struct* vma = NULL;

    // printk(KERN_INFO "Verified MMAP: do_verified_munmap   mm=%p, va=%016llx..%016llx\n", mm, vaddr, vaddr + sz - 1);

    // get the VMA struct
    vma = find_vma(mm, vaddr);
    if (!vma) {
        printk(KERN_INFO "Verified MMAP: do_verified_mmap   no VMA found.\n");
        return -EINVAL;
    }

    if (validate_range(vma, vaddr, sz)) {
        return -EINVAL;
    }

    // only works without PTI, otherwise kernel_to_user_pgdp(mm->pgd) is needed
    res = do_unmap_page(mm, mm->pgd, vaddr, sz);
    if (res != 0) {
        return res;
    }

    return res;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// VMA Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

static void vma_open(struct vm_area_struct* vma)
{
    printk(KERN_INFO "Verified MMAP: vma_open \n");
}

static void vma_close(struct vm_area_struct* vma)
{
    printk(KERN_INFO "Verified MMAP: vma_close \n");
}

static vm_fault_t vma_fault(struct vm_fault* vmf)
{
    // printk(KERN_INFO "Verified MMAP: triggered a vma_fault? This should not happen! Address = %lx\n", vmf->address);

    // Prevent any further fault attempts on this VMA
    vm_flags_set(vmf->vma, VM_DONTEXPAND | VM_PFNMAP);

    force_sig(SIGSEGV);
    return VM_FAULT_SIGSEGV | VM_FAULT_NOPAGE | VM_FAULT_OOM;
}

static vm_fault_t vma_huge_fault(struct vm_fault* vmf, unsigned order)
{
    printk(KERN_INFO "Verified MMAP: triggered a vma_huge_fault? This should not happen! Address = %lx\n", vmf->address);
    /// there should not be any faults here

    force_sig(SIGSEGV);
    return VM_FAULT_SIGSEGV | VM_FAULT_NOPAGE | VM_FAULT_RETRY;
}

static int vma_mremap(struct vm_area_struct* area)
{
    printk(KERN_INFO "Verified MMAP: called mremap? This should not happen!\n");
    return -EINVAL;
}

static int vma_mprotect(struct vm_area_struct* vma, unsigned long start,
    unsigned long end, unsigned long newflags)
{
    printk(KERN_INFO "Verified MMAP: called mprotect? This should not happen!\n");
    return -EINVAL;
}

static const char* vma_name(struct vm_area_struct* vma)
{
    return "verified_mmap";
}

static struct vm_operations_struct vma_ops = {
    // void (*open)(struct vm_area_struct * area);
    .open = vma_open,
    /**
     * @close: Called when the VMA is being removed from the MM.
     * Context: User context.  May sleep.  Caller holds mmap_lock.
     */
    // void (*close)(struct vm_area_struct * area);
    .close = vma_close,
    /* Called any time before splitting to check if it's allowed */
    // int (*may_split)(struct vm_area_struct *area, unsigned long addr);
    .may_split = NULL,
    // int (*mremap)(struct vm_area_struct *area);
    .mremap = vma_mremap,
    /*
     * Called by mprotect() to make driver-specific permission
     * checks before mprotect() is finalised.   The VMA must not
     * be modified.  Returns 0 if mprotect() can proceed.
     */
    // int (*mprotect)(struct vm_area_struct *vma, unsigned long start,
    //         unsigned long end, unsigned long newflags);
    .mprotect = vma_mprotect,
    // vm_fault_t (*fault)(struct vm_fault *vmf);
    .fault = vma_fault,
    // vm_fault_t (*huge_fault)(struct vm_fault *vmf, unsigned int order);
    .huge_fault = NULL, // vma_huge_fault,
    // vm_fault_t (*map_pages)(struct vm_fault *vmf,
    //         pgoff_t start_pgoff, pgoff_t end_pgoff);
    //         unsigned long (*pagesize)(struct vm_area_struct * area);
    .map_pages = NULL,

    /* notification that a previously read-only page is about to become
     * writable, if an error is returned it will cause a SIGBUS */
    // vm_fault_t (*page_mkwrite)(struct vm_fault *vmf);
    .page_mkwrite = NULL,

    /* same as page_mkwrite when using VM_PFNMAP|VM_MIXEDMAP */
    // vm_fault_t (*pfn_mkwrite)(struct vm_fault *vmf);
    .pfn_mkwrite = NULL,

    /* called by access_process_vm when get_user_pages() fails, typically
     * for use by special VMAs. See also generic_access_phys() for a generic
     * implementation useful for any iomem mapping.
     */
    // int (*access)(struct vm_area_struct *vma, unsigned long addr,
    //           void *buf, int len, int write);
    .access = NULL,

    /* Called by the /proc/PID/maps code to ask the vma whether it
     * has a special name.  Returning non-NULL will also cause this
     * vma to be dumped unconditionally. */
    // const char *(*name)(struct vm_area_struct *vma);
    .name = vma_name,

#ifdef CONFIG_NUMA
    /*
     * set_policy() op must add a reference to any non-NULL @new mempolicy
     * to hold the policy upon return.  Caller should pass NULL @new to
     * remove a policy and fall back to surrounding context--i.e. do not
     * install a MPOL_DEFAULT policy, nor the task or system default
     * mempolicy.
     */
    // int (*set_policy)(struct vm_area_struct *vma, struct mempolicy *new);
    .set_policy = NULL,

    /*
     * get_policy() op must add reference [mpol_get()] to any policy at
     * (vma,addr) marked as MPOL_SHARED.  The shared policy infrastructure
     * in mm/mempolicy.c will do this automatically.
     * get_policy() must NOT add a ref if the policy at (vma,addr) is not
     * marked as MPOL_SHARED. vma policies are protected by the mmap_lock.
     * If no [shared/vma] mempolicy exists at the addr, get_policy() op
     * must return NULL--i.e., do not "fallback" to task or system default
     * policy.
     */
    // struct mempolicy *(*get_policy)(struct vm_area_struct *vma,
    //                 unsigned long addr, pgoff_t *ilx);
    .get_policy = NULL,
#endif
    /*
     * Called by vm_normal_page() for special PTEs to find the
     * page for @addr.  This is useful if the default behavior
     * (using pte_page()) would not find the correct page.
     */
    // struct page *(*find_special_page)(struct vm_area_struct *vma,
    //                   unsigned long addr);
    .find_special_page = NULL,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Proc File Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

static int proc_handle_open(struct inode* inode, struct file* file)
{
    printk(KERN_INFO "Verified MMAP: proc_handle_open\n");

    /* Direct Access, avoiding the page cache */
    inode->i_flags = S_DAX;
    return 0;
}

static int proc_handle_release(struct inode* inode, struct file* file)
{
    return 0;
}

static long proc_handle_ioctl(struct file*, unsigned int cmd, unsigned long argp)
{
    int res;
    // printk(KERN_INFO "Verified MMAP: proc_handle_ioctl\n");

    // copy the arguments from user space
    union verified_mmap_ioctl_args args;
    res = copy_from_user(&args, (void __user*)argp, sizeof(args));
    if (res != 0) {
        return -EFAULT;
    }

    struct mm_struct* mm = current->mm;
    if (mm == NULL) {
        printk(KERN_INFO "Verified MMAP: current->mm was null!\n");
    }

    // then if its NULL, we can create our own VMA struct and insert it
    // or we could use __get_unmapped_area to get a free memory region

    // take the mmap lock, this seems to guard all mmap operations
    if (mmap_write_lock_killable(mm)) {
        printk(KERN_INFO "Verified MMAP: failed to take the mm lock!\n");
        return -EINTR;
    }

    switch (cmd) {
    case CMD_MMAP:
        res = do_verified_mmap(mm, args.mmap_args.vaddr, args.mmap_args.sz, args.mmap_args.flags);
        break;
    case CMD_MPROTECT:
        res = do_verified_mprotect(mm, args.mprotect_args.vaddr, args.mprotect_args.sz, args.mprotect_args.flags);
        break;
    case CMD_MUNMAP:
        res = do_verified_munmap(mm, args.munmap_args.vaddr, args.munmap_args.sz);
        break;
    default:
        res = -EINVAL;
    }

    // unlock the mmap lock
    mmap_write_unlock(mm);

    return res;
}

// this should be called when we initialize the struct
static int proc_handle_mmap(struct file* file, struct vm_area_struct* vma)
{
    printk(KERN_INFO "Verified MMAP: proc_handle_mmap\n");

    // let's set this to be locked
    vm_flags_set(vma, VM_LOCKED | VM_DONTEXPAND | VM_NOHUGEPAGE);

    // vma->vm_flags |= VM_LOCKED | VM_DONTEXPAND;

    // here check whether the range matches!

    // we're not calling the mmap handler here

    // we overwrite the VMA operations, so we can catch any mmfault or alike.
    vma->vm_ops = &vma_ops;

    return 0;
}

// TODO: we could probably use this function to hard code some memory regions.
// static int handle_proc_get_unmapped_area(struct file* file, unsigned long orig_addr, unsigned long len, unsigned long pgoff, unsigned long flags)
// {
//     printk(KERN_INFO "Verified MMAP: handle_proc_get_unmapped_area\n");
//     return 0;
// }

static struct proc_ops proc_ops = {
    .proc_flags = 0,
    // int (*proc_open)(struct inode *, struct file *);
    .proc_open = proc_handle_open,
    // ssize_t (*proc_read)(struct file *, char __user *, size_t, loff_t *);
    .proc_read = NULL,
    // ssize_t (*proc_read_iter)(struct kiocb *, struct iov_iter *);
    .proc_read_iter = NULL,
    // ssize_t (*proc_write)(struct file *, const char __user *, size_t, loff_t *);
    .proc_write = NULL,
    /* mandatory unless nonseekable_open() or equivalent is used */
    // loff_t (*proc_lseek)(struct file *, loff_t, int);
    .proc_lseek = NULL,
    // int (*proc_release)(struct inode *, struct file *);
    .proc_release = proc_handle_release,
    // __poll_t (*proc_poll)(struct file *, struct poll_table_struct *);
    .proc_poll = NULL,
    // long (*proc_ioctl)(struct file *, unsigned int, unsigned long);
    .proc_ioctl = proc_handle_ioctl,
#ifdef CONFIG_COMPAT
    // long (*proc_compat_ioctl)(struct file *, unsigned int, unsigned long);
    .proc_compat_ioctl = proc_handle_ioctl,
#endif
    // int (*proc_mmap)(struct file *, struct vm_area_struct *);
    .proc_mmap = proc_handle_mmap,
    // unsigned long (*proc_get_unmapped_area)(struct file *, unsigned long, unsigned long, unsigned long, unsigned long);
    // .proc_get_unmapped_area = handle_proc_get_unmapped_area,
};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Module init and exit
////////////////////////////////////////////////////////////////////////////////////////////////////

// Custom init and exit methods
static int __init module_start(void)
{
    printk(KERN_INFO "Verified MMAP: initializing module\n");

#ifdef CONFIG_USE_VELOSIRAPTOR
    printk(KERN_INFO "Verified MMAP: initializing module (velosiraptor)\n");
#elif defined(CONFIG_USE_VERIFIED)
    printk(KERN_INFO "Verified MMAP: initializing module (verified)\n");
#elif defined(CONFIG_USE_VERIFIED_NORECLAIM)
    printk(KERN_INFO "Verified MMAP: initializing module (verified+noreclaim)\n");
#else
    printk(KERN_INFO "Verified MMAP: initializing module (????)\n");
    #error "Unknown configuration specified"
    return -1;
#endif

#ifdef CONFIG_MITIGATION_PAGE_TABLE_ISOLATION
    // if the kernel is compiled with PTI and it is enabled, then we need to
    // also modify the user space page table. Now, in Linux, this is done by
    // copying some entries on the top level. see  pgd_prepopulate_user_pmd().
    if (boot_cpu_has(X86_FEATURE_PTI)) {
        printk(KERN_INFO "Verified MMAP: Page Table Isolation is enabled! Disable with `nopti` to cmdline.\n");
        return -EINVAL;
    }
#endif

#ifdef CONFIG_X86_KERNEL_IBT
    // check whether we have IBT enabled, this may infere with the way to lookup the TLB invalidation
    // function
    if (cpu_feature_enabled(X86_FEATURE_IBT)) {
        printk(KERN_INFO "Verified MMAP: Indirect Branch Target is enabled! Disable with `ibt=off` to cmdline.\n");
        return -EINVAL;
    }
#endif

    if (find_tlb_invalidate_symbol()) {
        printk(KERN_INFO "Verified MMAP: Could not retrieve tlb_mm_invalidate_range address\n");
        return -EINVAL;
    }

    if (pgtable_l5_enabled()) {
        printk(KERN_INFO "Verified MMAP: PML5 is enabled! Disable with `no5lvl` to cmdline.\n");
        return -EINVAL;
    }

    proc_entry = proc_create("verified_mmap", 0777, NULL, &proc_ops);
    if (proc_entry == NULL) {
        printk(KERN_INFO "Verified MMAP Interface failed to create proc entry.\n");
        return -ENOMEM;
    }

    printk(KERN_INFO "Verified MMAP: Module initialized successfully.\n");

    return 0;
}
static void __exit module_stop(void)
{
    if (proc_entry != NULL)
        proc_remove(proc_entry);
    printk(KERN_INFO "Verified MMAP Interface unloaded.\n");
}

module_init(module_start);
module_exit(module_stop);

// Module metadata
MODULE_AUTHOR("Reto Achermann");
MODULE_DESCRIPTION("Verified MMAP Interface");
MODULE_LICENSE("GPL");