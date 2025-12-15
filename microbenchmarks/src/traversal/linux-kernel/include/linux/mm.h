/* SPDX-License-Identifier: GPL-2.0 */
#ifndef _LINUX_MM_H
#define _LINUX_MM_H

#include <stddef.h>
#include <linux/mm_types.h>
#include <linux/pgtable.h>
#include <linux/gfp.h>

/*
 * vm_fault is filled by the pagefault handler and passed to the vma's
 * ->fault function. The vma's ->fault is responsible for returning a bitmask
 * of VM_FAULT_xxx flags that give details about how the fault was handled.
 *
 * MM layer fills up gfp_mask for page allocations but fault handler might
 * alter it if its implementation requires a different allocation context.
 *
 * pgoff should be used in favour of virtual_address, if possible.
 */
struct vm_fault {
	const struct {
		struct vm_area_struct *vma;	/* Target VMA */
		gfp_t gfp_mask;			/* gfp mask to be used for allocations */
		pgoff_t pgoff;			/* Logical page offset based on vma */
		unsigned long address;		/* Faulting virtual address - masked */
		unsigned long real_address;	/* Faulting virtual address - unmasked */
	};
	enum fault_flag flags;		/* FAULT_FLAG_xxx flags
					 * XXX: should really be 'const' */
	pmd_t *pmd;			/* Pointer to pmd entry matching
					 * the 'address' */
	pud_t *pud;			/* Pointer to pud entry matching
					 * the 'address'
					 */
	union {
		pte_t orig_pte;		/* Value of PTE at the time of fault */
		pmd_t orig_pmd;		/* Value of PMD at the time of fault,
					 * used by PMD fault only.
					 */
	};

	struct page *cow_page;		/* Page handler may use for COW fault */
	struct page *page;		/* ->fault handlers should return a
					 * page here, unless VM_FAULT_NOPAGE
					 * is set (which is also implied by
					 * VM_FAULT_ERROR).
					 */
	/* These three entries are valid only while holding ptl lock */
	pte_t *pte;			/* Pointer to pte entry matching
					 * the 'address'. NULL if the page
					 * table hasn't been allocated.
					 */
	int *ptl;		/* Page table lock.
	//				 * Protects pte page table if 'pte'
	//				 * is not NULL, otherwise pmd.
	//				 */
	pgtable_t prealloc_pte;		/* Pre-allocated pte page table.
					 * vm_ops->map_pages() sets up a page
					 * table from atomic context.
					 * do_fault_around() pre-allocates
					 * page table to avoid allocation from
					 * atomic context.
					 */
};

pte_t *__pte_offset_map(pmd_t *pmd, unsigned long addr, pmd_t *pmdvalp);
static inline pte_t *pte_offset_map(pmd_t *pmd, unsigned long addr)
{
	return __pte_offset_map(pmd, addr, NULL);
}

pte_t *pte_offset_map_nolock(struct mm_struct *mm, pmd_t *pmd,
			unsigned long addr, spinlock_t **ptlp);

#if defined(CONFIG_MMU)

static inline int __p4d_alloc(struct mm_struct *mm, pgd_t *pgd,
						unsigned long address)
{
	return 0;
}

int __pmd_alloc(struct mm_struct *mm, pud_t *pud, unsigned long address);
int __pud_alloc(struct mm_struct *mm, p4d_t *p4d, unsigned long address);

static inline p4d_t *p4d_alloc(struct mm_struct *mm, pgd_t *pgd,
		unsigned long address)
{
	return (pgd_none(*pgd) && __p4d_alloc(mm, pgd, address)) ?
		NULL : p4d_offset(pgd, address);
}

static inline pud_t *pud_alloc(struct mm_struct *mm, p4d_t *p4d,
		unsigned long address)
{
	return (p4d_none(*p4d) && __pud_alloc(mm, p4d, address)) ?
		NULL : pud_offset(p4d, address);
}

static inline pmd_t *pmd_alloc(struct mm_struct *mm, pud_t *pud, unsigned long address)
{
	return (pud_none(*pud) && __pmd_alloc(mm, pud, address))?
		NULL: pmd_offset(pud, address);
}

int __pte_alloc(struct mm_struct *mm, pmd_t *pmd);
int __pte_alloc_kernel(pmd_t *pmd);

#define pte_alloc(mm, pmd) (unlikely(pmd_none(*(pmd))) && __pte_alloc(mm, pmd))

#define pte_alloc_map(mm, pmd, address)			\
	(pte_alloc(mm, pmd) ? NULL : pte_offset_map(pmd, address))

#define pte_alloc_map_lock(mm, pmd, address, ptlp)	\
	(pte_alloc(mm, pmd) ?			\
		 NULL : pte_offset_map_lock(mm, pmd, address, ptlp))

#define pte_alloc_kernel(pmd, address)			\
	((unlikely(pmd_none(*(pmd))) && __pte_alloc_kernel(pmd))? \
		NULL: pte_offset_kernel(pmd, address))


pte_t *__pte_offset_map_lock(struct mm_struct *mm, pmd_t *pmd,
			unsigned long addr, spinlock_t **ptlp);
static inline pte_t *pte_offset_map_lock(struct mm_struct *mm, pmd_t *pmd,
			unsigned long addr, spinlock_t **ptlp)
{
	pte_t *pte;

	return __pte_offset_map_lock(mm, pmd, addr, ptlp);
}

#define pte_unmap_unlock(pte, ptl)	do {		\
	pte_unmap(pte);					\
} while (0)

#endif /* CONFIG_MMU */

static inline spinlock_t *pte_lockptr(struct mm_struct *mm, pmd_t *pmd)
{
	return NULL;
	// return ptlock_ptr(page_ptdesc(pmd_page(*pmd)));
}


int __pud_alloc(struct mm_struct *mm, p4d_t *p4d, unsigned long address);
int __pmd_alloc(struct mm_struct *mm, pud_t *pud, unsigned long address);

#endif /* _LINUX_MM_H */