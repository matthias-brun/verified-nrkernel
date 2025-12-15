#include <stddef.h>
#include <stdlib.h>
#include <assert.h>

#include "config.h"

#include<asm/pgalloc.h>
#include<linux/pgtable.h>
#include<linux/mm_types.h>
#include<linux/mm.h>
#include<linux/align.h>
#include<linux/pagemap.h>

#include<pthread.h>

static pthread_spinlock_t lock;

pteval_t __supported_pte_mask = ~0;


/*
 * On entry, we hold either the VMA lock or the mmap_lock
 * (FAULT_FLAG_VMA_LOCK tells you which).  If VM_FAULT_RETRY is set in
 * the result, the mmap_lock is not held on exit.  See filemap_fault()
 * and __folio_lock_or_retry().
 */
static vm_fault_t __handle_mm_fault(struct vm_area_struct *vma,
		unsigned long address, unsigned int flags, struct page *page)
{
	struct vm_fault vmf = {
		.vma = vma,
		.address = address & PAGE_MASK,
		.real_address = address,
		.flags = flags,
		.pgoff = linear_page_index(vma, address),
		.gfp_mask = 0, //__get_fault_gfp_mask(vma),
	};
	struct mm_struct *mm = vma->vm_mm;
	unsigned long vm_flags = vma->vm_flags;
	pgd_t *pgd;
	p4d_t *p4d;
	vm_fault_t ret;

	pgd = pgd_offset(mm, address);

	p4d = p4d_alloc(mm, pgd, address);
	if (!p4d)
		return VM_FAULT_OOM;

	vmf.pud = pud_alloc(mm, p4d, address);
	if (!vmf.pud)
		return VM_FAULT_OOM;

	vmf.pmd = pmd_alloc(mm, vmf.pud, address);
	if (!vmf.pmd)
		return VM_FAULT_OOM;

	vmf.pte = pte_alloc_map(mm, vmf.pmd, address);
	if (!vmf.pte) {
		return VM_FAULT_OOM;
	}

	set_pte(vmf.pte, pfn_pte(address >> PAGE_SHIFT, __pgprot(flags)));
	return 0;
}


void *linux_bench_init() {

	pthread_spin_init(&lock, PTHREAD_PROCESS_SHARED);

    // allocate vma_area
    // allocate mm_struct
    struct vm_area_struct *vma = calloc(1, sizeof(struct vm_area_struct));
    if (vma == NULL) {
        return NULL;
    }

    struct mm_struct *mm = calloc(1, sizeof(struct mm_struct));
    if (mm == NULL) {
        free(vma);
        return NULL;
    }

	mm->pgd = pgd_alloc(mm);

    vma->vm_mm = mm;

    return vma;
}

int linux_bench_map_one(void *st, unsigned long addr, unsigned long paddr) {
    pthread_spin_lock(&lock);
	struct page page =  {
        .addr = paddr
    };
   int r = __handle_mm_fault((struct vm_area_struct *)st, addr, FAULT_FLAG_WRITE, &page);
	pthread_spin_unlock(&lock);
   return r;
}

int linux_bench_protect_one(void *st, unsigned long addr, unsigned long _paddr) {
	pthread_spin_lock(&lock);
	struct vm_area_struct *vma = st;

    struct mm_struct *mm = vma->vm_mm;

    pgd_t *pgd;
	p4d_t *p4d;
    pud_t *pud;
    pmd_t *pmd;
	pte_t *pte;

	pgd = pgd_offset(mm, addr);
	if (pgd_none_or_clear_bad(pgd)) {
		pthread_spin_unlock(&lock);
		return 1;
	}

	p4d = p4d_offset(pgd, addr);
	if (p4d_none_or_clear_bad(p4d)) {
		pthread_spin_unlock(&lock);
		return 2;
	}

	pud = pud_offset(p4d, addr);
	if (pud_none_or_clear_bad(pud)) {
		pthread_spin_unlock(&lock);
		return 3;
	}

	pmd = pmd_offset(pud, addr);
	if (pmd_none(*pmd)) {
		pthread_spin_unlock(&lock);
		return 4;
	}

	spinlock_t *lck;
	pte = pte_offset_map_nolock(mm, pmd, addr, &lck);
	if (pte_none(*pte)) {
		pthread_spin_unlock(&lock);
		return 5;
	}

	// update the PTE
	set_pte(pte, pte_mkexec(*pte));

	pthread_spin_unlock(&lock);
	return 0;
}

int linux_bench_unmap_one(void *st, unsigned long addr, unsigned long _paddr) {
    pthread_spin_lock(&lock);
	struct vm_area_struct *vma = st;

    struct mm_struct *mm = vma->vm_mm;

    pgd_t *pgd;
	p4d_t *p4d;
    pud_t *pud;
    pmd_t *pmd;
	pte_t *pte;

	vm_fault_t ret;

	pgd = pgd_offset(mm, addr);
	if (pgd_none_or_clear_bad(pgd)) {
		pthread_spin_unlock(&lock);
		return 1;
	}

	p4d = p4d_offset(pgd, addr);
	if (p4d_none_or_clear_bad(p4d)) {
		pthread_spin_unlock(&lock);
		return 2;
	}

	pud = pud_offset(p4d, addr);
	if (pud_none_or_clear_bad(pud)) {
		pthread_spin_unlock(&lock);
		return 3;
	}

	pmd = pmd_offset(pud, addr);
	if (pmd_none(*pmd)) {
		pthread_spin_unlock(&lock);
		return 4;
	}

	spinlock_t *lck;
	pte = pte_offset_map_nolock(mm, pmd, addr, &lck);
	if (pte_none(*pte)) {
		pthread_spin_unlock(&lock);
		return 5;
	}

	pte_clear(mm, addr, pte);

	pthread_spin_unlock(&lock);
    return 0;
}

