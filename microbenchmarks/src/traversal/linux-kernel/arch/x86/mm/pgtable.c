// SPDX-License-Identifier: GPL-2.0

#include "../../../config.h"

#include <linux/mm.h>
#include <linux/gfp.h>
#include <asm/pgalloc.h>

#ifdef CONFIG_DYNAMIC_PHYSICAL_MASK
phys_addr_t physical_mask __ro_after_init = (1ULL << __PHYSICAL_MASK_SHIFT) - 1;
EXPORT_SYMBOL(physical_mask);
#endif

#define PGTABLE_HIGHMEM 0

gfp_t __userpte_alloc_gfp = GFP_PGTABLE_USER | PGTABLE_HIGHMEM;

pgtable_t pte_alloc_one(struct mm_struct *mm)
{
	return __pte_alloc_one(mm, __userpte_alloc_gfp);
}

static inline pgd_t *_pgd_alloc(void)
{
	void *mem=aligned_alloc(PAGE_SIZE, PAGE_SIZE);
	memset(mem, 0, PAGE_SIZE);
	return mem;
}

static inline void _pgd_free(pgd_t *pgd)
{
	free(pgd);
}

pgd_t *pgd_alloc(struct mm_struct *mm)
{
	return _pgd_alloc();
}

void pgd_free(struct mm_struct *mm, pgd_t *pgd)
{
	// pgd_mop_up_pmds(mm, pgd);
	// pgd_dtor(pgd);
	paravirt_pgd_free(mm, pgd);
	_pgd_free(pgd);
}

/*
 * Used to set accessed or dirty bits in the page table entries
 * on other architectures. On x86, the accessed and dirty bits
 * are tracked by hardware. However, do_wp_page calls this function
 * to also make the pte writeable at the same time the dirty bit is
 * set. In that case we do actually need to write the PTE.
 */
int ptep_set_access_flags(struct vm_area_struct *vma,
			  unsigned long address, pte_t *ptep,
			  pte_t entry, int dirty)
{
	int changed = !pte_same(*ptep, entry);

	if (changed && dirty)
		set_pte(ptep, entry);

	return changed;
}


pte_t pte_mkwrite(pte_t pte, struct vm_area_struct *vma)
{
	if (vma->vm_flags & VM_SHADOW_STACK)
		return pte_mkwrite_shstk(pte);

	pte = pte_mkwrite_novma(pte);

	return pte_clear_saveddirty(pte);
}

