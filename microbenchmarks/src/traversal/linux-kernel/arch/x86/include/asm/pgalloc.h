/* SPDX-License-Identifier: GPL-2.0 */
#ifndef _ASM_X86_PGALLOC_H
#define _ASM_X86_PGALLOC_H

// #include <linux/threads.h>
#include <linux/mm.h>		/* for struct page */
#include <linux/pagemap.h>

#define __HAVE_ARCH_PTE_ALLOC_ONE
#define __HAVE_ARCH_PGD_FREE
#include <asm-generic/pgalloc.h>

static inline int  __paravirt_pgd_alloc(struct mm_struct *mm) { return 0; }

#ifdef CONFIG_PARAVIRT_XXL
#include <asm/paravirt.h>
#else
#define paravirt_pgd_alloc(mm)	__paravirt_pgd_alloc(mm)
static inline void paravirt_pgd_free(struct mm_struct *mm, pgd_t *pgd) {}
static inline void paravirt_alloc_pte(struct mm_struct *mm, unsigned long pfn)	{}
static inline void paravirt_alloc_pmd(struct mm_struct *mm, unsigned long pfn)	{}
static inline void paravirt_alloc_pmd_clone(unsigned long pfn, unsigned long clonepfn,
					    unsigned long start, unsigned long count) {}
static inline void paravirt_alloc_pud(struct mm_struct *mm, unsigned long pfn)	{}
static inline void paravirt_alloc_p4d(struct mm_struct *mm, unsigned long pfn)	{}
static inline void paravirt_release_pte(unsigned long pfn) {}
static inline void paravirt_release_pmd(unsigned long pfn) {}
static inline void paravirt_release_pud(unsigned long pfn) {}
static inline void paravirt_release_p4d(unsigned long pfn) {}
#endif


/*
 * Allocate and free page tables.
 */
extern pgd_t *pgd_alloc(struct mm_struct *);
extern void pgd_free(struct mm_struct *mm, pgd_t *pgd);

extern pgtable_t pte_alloc_one(struct mm_struct *);

// extern void ___pte_free_tlb(struct mmu_gather *tlb, struct page *pte);

// static inline void __pte_free_tlb(struct mmu_gather *tlb, struct page *pte,
// 				  unsigned long address)
// {
// 	___pte_free_tlb(tlb, pte);
// }

static inline void pmd_populate_kernel(struct mm_struct *mm,
				       pmd_t *pmd, pte_t *pte)
{
	paravirt_alloc_pte(mm, __pa(pte) >> PAGE_SHIFT);
	set_pmd(pmd, __pmd(__pa(pte) | _PAGE_TABLE));
}

static inline void pmd_populate_kernel_safe(struct mm_struct *mm,
				       pmd_t *pmd, pte_t *pte)
{
	paravirt_alloc_pte(mm, __pa(pte) >> PAGE_SHIFT);
	set_pmd_safe(pmd, __pmd(__pa(pte) | _PAGE_TABLE));
}

static inline void pmd_populate(struct mm_struct *mm, pmd_t *pmd, pte_t *pte)
{
	paravirt_alloc_pte(mm, __pa(pte) >> PAGE_SHIFT);
	set_pmd(pmd, __pmd(((pteval_t)__pa(pte)) | _PAGE_TABLE));
}

#if CONFIG_PGTABLE_LEVELS > 2
#ifdef CONFIG_X86_PAE
extern void pud_populate(struct mm_struct *mm, pud_t *pudp, pmd_t *pmd);
#else	/* !CONFIG_X86_PAE */
static inline void pud_populate(struct mm_struct *mm, pud_t *pud, pmd_t *pmd)
{
	paravirt_alloc_pmd(mm, __pa(pmd) >> PAGE_SHIFT);
	set_pud(pud, __pud(_PAGE_TABLE | __pa(pmd)));
}

static inline void pud_populate_safe(struct mm_struct *mm, pud_t *pud, pmd_t *pmd)
{
	paravirt_alloc_pmd(mm, __pa(pmd) >> PAGE_SHIFT);
	set_pud_safe(pud, __pud(_PAGE_TABLE | __pa(pmd)));
}
#endif	/* CONFIG_X86_PAE */

#if CONFIG_PGTABLE_LEVELS > 3
static inline void p4d_populate(struct mm_struct *mm, p4d_t *p4d, pud_t *pud)
{
	paravirt_alloc_pud(mm, __pa(pud) >> PAGE_SHIFT);
	set_p4d(p4d, __p4d(_PAGE_TABLE | __pa(pud)));
}

static inline void p4d_populate_safe(struct mm_struct *mm, p4d_t *p4d, pud_t *pud)
{
	paravirt_alloc_pud(mm, __pa(pud) >> PAGE_SHIFT);
	set_p4d_safe(p4d, __p4d(_PAGE_TABLE | __pa(pud)));
}

#endif	/* CONFIG_PGTABLE_LEVELS > 3 */
#endif	/* CONFIG_PGTABLE_LEVELS > 2 */

#endif /* _ASM_X86_PGALLOC_H */