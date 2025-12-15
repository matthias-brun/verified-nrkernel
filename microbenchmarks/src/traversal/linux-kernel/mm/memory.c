
// SPDX-License-Identifier: GPL-2.0-only
/*
 *  linux/mm/memory.c
 *
 *  Copyright (C) 1991, 1992, 1993, 1994  Linus Torvalds
 */

/*
 * demand-loading started 01.12.91 - seems it is high on the list of
 * things wanted, and it should be easy to implement. - Linus
 */

/*
 * Ok, demand-loading was easy, shared pages a little bit tricker. Shared
 * pages started 02.12.91, seems to work. - Linus.
 *
 * Tested sharing by executing about 30 /bin/sh: under the old kernel it
 * would have taken more than the 6M I have free, but it worked well as
 * far as I could see.
 *
 * Also corrected some "invalidate()"s - I wasn't doing enough of them.
 */

/*
 * Real VM (paging to/from disk) started 18.12.91. Much more work and
 * thought has to go into this. Oh, well..
 * 19.12.91  -  works, somewhat. Sometimes I get faults, don't know why.
 *		Found it. Everything seems to work now.
 * 20.12.91  -  Ok, making the swap-device changeable like the root.
 */

/*
 * 05.04.94  -  Multi-page memory management added for v1.1.
 *              Idea by Alex Bligh (alex@cconcepts.co.uk)
 *
 * 16.07.99  -  Support of BIGMEM added by Gerhard Wichert, Siemens AG
 *		(Gerhard.Wichert@pdb.siemens.de)
 *
 * Aug/Sep 2004 Changed to four level page tables (Andi Kleen)
 */


#include "../config.h"
#include<errno.h>

#include <linux/mm.h>
#include <asm/pgalloc.h>
#include <asm-generic/pgalloc.h>


/*
 * Allocate page upper directory.
 * We've already handled the fast-path in-line.
 */
int __pud_alloc(struct mm_struct *mm, p4d_t *p4d, unsigned long address)
{
	pud_t *new = pud_alloc_one(mm, address);
	if (!new)
		return -ENOMEM;

	// spin_lock(&mm->page_table_lock);
	if (!p4d_present(*p4d)) {
		// mm_inc_nr_puds(mm);
		// smp_wmb(); /* See comment in pmd_install() */
		p4d_populate(mm, p4d, new);
	} else	/* Another has populated it */
		pud_free(mm, new);
	// spin_unlock(&mm->page_table_lock);
	return 0;
}

/*
 * Allocate page middle directory.
 * We've already handled the fast-path in-line.
 */
int __pmd_alloc(struct mm_struct *mm, pud_t *pud, unsigned long address)
{
	// spinlock_t *ptl;
	pmd_t *new = pmd_alloc_one(mm, address);
	if (!new)
		return -ENOMEM;

	// ptl = pud_lock(mm, pud);
	if (!pud_present(*pud)) {
		// mm_inc_nr_pmds(mm);
		// smp_wmb(); /* See comment in pmd_install() */
		pud_populate(mm, pud, new);
	} else {	/* Another has populated it */
		pmd_free(mm, new);
	}
	// spin_unlock(ptl);
	return 0;
}

void pmd_install(struct mm_struct *mm, pmd_t *pmd, pgtable_t *pte)
{
	// spinlock_t *ptl = pmd_lock(mm, pmd);

	if (likely(pmd_none(*pmd))) {	/* Has another populated it ? */
		// mm_inc_nr_ptes(mm);
		// smp_wmb(); /* Could be smp_wmb__xxx(before|after)_spin_lock */
		pmd_populate(mm, pmd, *pte);
		*pte = NULL;
	}
	// spin_unlock(ptl);
}
int __pte_alloc(struct mm_struct *mm, pmd_t *pmd)
{
	pgtable_t new = pte_alloc_one(mm);
	if (!new)
		return -ENOMEM;

	pmd_install(mm, pmd, &new);
	if (new)
		pte_free(mm, new);
	return 0;
}
