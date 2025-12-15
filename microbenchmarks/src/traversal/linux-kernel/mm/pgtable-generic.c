// SPDX-License-Identifier: GPL-2.0
/*
 *  mm/pgtable-generic.c
 *
 *  Generic pgtable methods declared in linux/pgtable.h
 *
 *  Copyright (C) 2010  Linus Torvalds
 */

#include <stdlib.h>

#include "../config.h"

#include <linux/pgtable.h>
#include <linux/mm.h>

/*
 * If a p?d_bad entry is found while walking page tables, report
 * the error, before resetting entry to p?d_none.  Usually (but
 * very seldom) called out from the p?d_none_or_clear_bad macros.
 */

void pgd_clear_bad(pgd_t *pgd)
{
	pgd_ERROR(*pgd);
	pgd_clear(pgd);
}

#ifndef __PAGETABLE_P4D_FOLDED
void p4d_clear_bad(p4d_t *p4d)
{
	p4d_ERROR(*p4d);
	p4d_clear(p4d);
}
#endif

#ifndef __PAGETABLE_PUD_FOLDED
void pud_clear_bad(pud_t *pud)
{
	pud_ERROR(*pud);
	pud_clear(pud);
}
#endif

/*
 * Note that the pmd variant below can't be stub'ed out just as for p4d/pud
 * above. pmd folding is special and typically pmd_* macros refer to upper
 * level even when folded
 */
void pmd_clear_bad(pmd_t *pmd)
{
	pmd_ERROR(*pmd);
	pmd_clear(pmd);
}


#ifndef __HAVE_ARCH_PTEP_CLEAR_FLUSH
pte_t ptep_clear_flush(struct vm_area_struct *vma, unsigned long address,
		       pte_t *ptep)
{
	struct mm_struct *mm = (vma)->vm_mm;
	pte_t pte;
	pte = ptep_get_and_clear(mm, address, ptep);
	// if (pte_accessible(mm, pte))
	// 	flush_tlb_page(vma, address);
	return pte;
}
#endif



static unsigned long pmdp_get_lockless_start(void) { return 0; }
static void pmdp_get_lockless_end(unsigned long irqflags) { }


pte_t *__pte_offset_map(pmd_t *pmd, unsigned long addr, pmd_t *pmdvalp)
{
	unsigned long irqflags;
	pmd_t pmdval;

	irqflags = pmdp_get_lockless_start();
	pmdval = pmdp_get_lockless(pmd);
	pmdp_get_lockless_end(irqflags);

	if (pmdvalp)
		*pmdvalp = pmdval;
	if (unlikely(pmd_none(pmdval) || is_pmd_migration_entry(pmdval)))
		goto nomap;
	if (unlikely(pmd_trans_huge(pmdval) || pmd_devmap(pmdval)))
		goto nomap;
	if (unlikely(pmd_bad(pmdval))) {
		pmd_clear_bad(pmd);
		goto nomap;
	}
	return __pte_map(&pmdval, addr);
nomap:
	return NULL;
}

pte_t *pte_offset_map_nolock(struct mm_struct *mm, pmd_t *pmd,
			     unsigned long addr, spinlock_t **ptlp)
{
	pmd_t pmdval;
	pte_t *pte;

	pte = __pte_offset_map(pmd, addr, &pmdval);
	if (likely(pte))
		*ptlp = pte_lockptr(mm, &pmdval);
	return pte;
}

/*
 * pte_offset_map_lock(mm, pmd, addr, ptlp), and its internal implementation
 * __pte_offset_map_lock() below, is usually called with the pmd pointer for
 * addr, reached by walking down the mm's pgd, p4d, pud for addr: either while
 * holding mmap_lock or vma lock for read or for write; or in truncate or rmap
 * context, while holding file's i_mmap_lock or anon_vma lock for read (or for
 * write). In a few cases, it may be used with pmd pointing to a pmd_t already
 * copied to or constructed on the stack.
 *
 * When successful, it returns the pte pointer for addr, with its page table
 * kmapped if necessary (when CONFIG_HIGHPTE), and locked against concurrent
 * modification by software, with a pointer to that spinlock in ptlp (in some
 * configs mm->page_table_lock, in SPLIT_PTLOCK configs a spinlock in table's
 * struct page).  pte_unmap_unlock(pte, ptl) to unlock and unmap afterwards.
 *
 * But it is unsuccessful, returning NULL with *ptlp unchanged, if there is no
 * page table at *pmd: if, for example, the page table has just been removed,
 * or replaced by the huge pmd of a THP.  (When successful, *pmd is rechecked
 * after acquiring the ptlock, and retried internally if it changed: so that a
 * page table can be safely removed or replaced by THP while holding its lock.)
 *
 * pte_offset_map(pmd, addr), and its internal helper __pte_offset_map() above,
 * just returns the pte pointer for addr, its page table kmapped if necessary;
 * or NULL if there is no page table at *pmd.  It does not attempt to lock the
 * page table, so cannot normally be used when the page table is to be updated,
 * or when entries read must be stable.  But it does take rcu_read_lock(): so
 * that even when page table is racily removed, it remains a valid though empty
 * and disconnected table.  Until pte_unmap(pte) unmaps and rcu_read_unlock()s
 * afterwards.
 *
 * pte_offset_map_nolock(mm, pmd, addr, ptlp), above, is like pte_offset_map();
 * but when successful, it also outputs a pointer to the spinlock in ptlp - as
 * pte_offset_map_lock() does, but in this case without locking it.  This helps
 * the caller to avoid a later pte_lockptr(mm, *pmd), which might by that time
 * act on a changed *pmd: pte_offset_map_nolock() provides the correct spinlock
 * pointer for the page table that it returns.  In principle, the caller should
 * recheck *pmd once the lock is taken; in practice, no callsite needs that -
 * either the mmap_lock for write, or pte_same() check on contents, is enough.
 *
 * Note that free_pgtables(), used after unmapping detached vmas, or when
 * exiting the whole mm, does not take page table lock before freeing a page
 * table, and may not use RCU at all: "outsiders" like khugepaged should avoid
 * pte_offset_map() and co once the vma is detached from mm or mm_users is zero.
 */
pte_t *__pte_offset_map_lock(struct mm_struct *mm, pmd_t *pmd,
			     unsigned long addr, spinlock_t **ptlp)
{
	spinlock_t *ptl;
	pmd_t pmdval;
	pte_t *pte;
again:
	pte = __pte_offset_map(pmd, addr, &pmdval);
	if (unlikely(!pte))
		return pte;
	ptl = pte_lockptr(mm, &pmdval);
	// spin_lock(ptl);
	if (likely(pmd_same(pmdval, pmdp_get_lockless(pmd)))) {
		*ptlp = ptl;
		return pte;
	}
	pte_unmap_unlock(pte, ptl);
	goto again;
}