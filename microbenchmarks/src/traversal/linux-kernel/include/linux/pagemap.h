/* SPDX-License-Identifier: GPL-2.0 */
#ifndef _LINUX_PAGEMAP_H
#define _LINUX_PAGEMAP_H


static inline pgoff_t linear_page_index(struct vm_area_struct *vma,
					unsigned long address)
{
	pgoff_t pgoff;
	pgoff = (address - vma->vm_start) >> PAGE_SHIFT;
	pgoff += vma->vm_pgoff;
	return pgoff;
}

#endif /* _LINUX_PAGEMAP_H */