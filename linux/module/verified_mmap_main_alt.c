/*---------------------------------------------------------------------------*/
// Copyright (c) 2022 ETH Zurich.
// All rights reserved.
//
// This file is distributed under the terms in the attached LICENSE file.
// If you do not find this file, copies can be found by writing to:
// ETH Zurich D-INFK, Stampfenbachstrasse 114, CH-8092 Zurich. Attn: Systems Group
/*---------------------------------------------------------------------------*/

#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/cdev.h>
#include <linux/device.h>
#include <linux/fs.h>
#include <linux/version.h>
#include <asm/io.h>
#include <linux/mm.h>
#include <linux/pfn_t.h>
#include <linux/smp.h>

#include <asm/arch_gicv3.h>

#define FPGA_MEMORY_ADDRESS 0x10000000000ULL

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Adam S. Turowski");
MODULE_DESCRIPTION("Enzian FPGA memory driver.");
MODULE_VERSION("1");

struct mychar_device_data {
    struct cdev cdev;
    void *fpga_memory;
};

static int dev_major = 0;
static struct class *mychardev_class = NULL;
static struct mychar_device_data mychardev_data;
DEFINE_MUTEX(enzian_memory_mmap_mutex);

int enzian_memory_open(struct inode *inode, struct file *file);
long int enzian_memory_ioctl(struct file *file, unsigned int cmd, unsigned long arg);
void enzian_memory_vma_open(struct vm_area_struct *vma);
void enzian_memory_vma_close(struct vm_area_struct *vma);
int enzian_memory_mmap(struct file *file, struct vm_area_struct *vma);
int enzian_memory_release(struct inode *inode, struct file *file);

int enzian_memory_open(struct inode *inode, struct file *file)
{
    inode->i_flags = S_DAX;
    return 0;
}

long int enzian_memory_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
    switch (cmd) {
    case 0: // L2 Cache Index Writeback Invalidate, SYS CVMCACHEWBIL2I, Xt
        asm volatile("sys #0,c11,c0,#5,%0 \n" :: "r" (arg));
        break;
    case 1: // L2 Cache Index Writeback, SYS CVMCACHEWBL2I, Xt
        asm volatile("sys #0,c11,c0,#6,%0 \n" :: "r" (arg));
        break;
    case 2: // L2 Cache Index Load Tag, SYS CVMCACHELTGL2I, Xt
        asm volatile("sys #0,c11,c0,#7,%0 \n" :: "r" (arg));
        break;
    case 3: // L2 Cache Index Store Tag, SYS CVMCACHESTGL2I, Xt
        asm volatile("sys #0,c11,c1,#0,%0 \n" :: "r" (arg));
        break;
    case 4: // L2 Cache Hit Invalidat, SYS CVMCACHEINVL2, Xt
        asm volatile("sys #0,c11,c1,#1,%0 \n" :: "r" (arg));
        break;
    case 5: // L2 Cache Hit Writeback Invalidate, SYS CVMCACHEWBIL2, Xt <<<
        asm volatile("sys #0,c11,c1,#2,%0 \n" :: "r" (arg));
        break;
    case 6: // L2 Cache Hit Writeback, SYS CVMCACHEWBL2, Xt
        asm volatile("sys #0,c11,c1,#3,%0 \n" :: "r" (arg));
        break;
    case 7: // L2 Cache Fetch and Lock, SYS CVMCACHELCKL2, Xt
        asm volatile("sys #0,c11,c1,#4,%0 \n" :: "r" (arg));
        break;
    case 8: // uTLB read, SYS CVMCACHERDUTLB, Xt
        asm volatile("sys #0,c11,c1,#5,%0 \n" :: "r" (arg));
        break;
    case 9: // MTLB read, SYS CVMCACHERDMTLB, Xt
        asm volatile("sys #0,c11,c1,#6,%0 \n" :: "r" (arg));
        break;
    case 10: // PREFu, SYS CVMCACHEPREFUTLB, Xt
        asm volatile("sys #0,c11,c2,#0,%0 \n" :: "r" (arg));
        break;
    default:
        return -EINVAL;
    }
    return 0;
}

void enzian_memory_vma_open(struct vm_area_struct *vma)
{
}

void enzian_memory_vma_close(struct vm_area_struct *vma)
{
}

static vm_fault_t enzian_memory_fault(struct vm_fault *vmf)
{
    return VM_FAULT_SIGBUS;
}

static vm_fault_t enzian_memory_pmd_fault(struct vm_fault *vmf)
{
    pfn_t pfn;

    pfn = phys_to_pfn_t(FPGA_MEMORY_ADDRESS + (vmf->pgoff << PAGE_SHIFT), PFN_DEV | PFN_MAP);
    return vmf_insert_pfn_pmd(vmf, pfn, true);
}

#ifdef CONFIG_HAVE_ARCH_TRANSPARENT_HUGEPAGE_PUD
static vm_fault_t enzian_memory_pud_fault(struct vm_fault *vmf)
{
    pfn_t pfn;

    pfn = phys_to_pfn_t(FPGA_MEMORY_ADDRESS + (vmf->pgoff << PAGE_SHIFT), PFN_DEV | PFN_MAP);
    if (! pud_valid(*vmf->pud)) {
        int r = vmf_insert_pfn_pud(vmf, pfn, true);
        return r;
    }
    return 0;
}
#endif

static vm_fault_t enzian_memory_huge_fault(struct vm_fault *vmf,
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6,6,0)
        unsigned order)
#else
        enum page_entry_size pe_size)
#endif
{
    int r;

    r = VM_FAULT_SIGBUS;
    mutex_lock(&enzian_memory_mmap_mutex);
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6,6,0)
    if (order == PMD_ORDER) { // 2MB pages
#else
    if (pe_size == PE_SIZE_PMD) { // 2MB pages
#endif
        r = enzian_memory_pmd_fault(vmf);
    } else
#ifdef CONFIG_HAVE_ARCH_TRANSPARENT_HUGEPAGE_PUD
        r = enzian_memory_pud_fault(vmf); // 1GB pages
#else
        pr_err("Unsupported page size!\n");
#endif
    mutex_unlock(&enzian_memory_mmap_mutex);
    return r;
}

static struct vm_operations_struct enzian_memory_remap_vm_ops = {
    .open = enzian_memory_vma_open,
    .close = enzian_memory_vma_close,
    .fault = enzian_memory_fault,
    .huge_fault = enzian_memory_huge_fault
};

int enzian_memory_mmap(struct file *file, struct vm_area_struct *vma)
{
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6,4,0)
    vm_flags_set(vma, VM_PFNMAP);
#else
    vma->vm_flags |= VM_PFNMAP;
#endif
    vma->vm_ops = &enzian_memory_remap_vm_ops;
    enzian_memory_vma_open(vma);
    return 0;
}


struct file_operations fops = {
    .open = enzian_memory_open,
    .release = enzian_memory_release,
    .mmap = enzian_memory_mmap,
    .unlocked_ioctl = enzian_memory_ioctl,
};

static int __init enzian_memory_init(void)
{
    int err;
    dev_t dev;

    err = alloc_chrdev_region(&dev, 0, 1, "fpgamem");
    dev_major = MAJOR(dev);
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6,4,0)
    mychardev_class = class_create("fpgamem");
#else
    mychardev_class = class_create(THIS_MODULE, "fpgamem");
#endif
    cdev_init(&mychardev_data.cdev, &fops);
    mychardev_data.cdev.owner = THIS_MODULE;
    cdev_add(&mychardev_data.cdev, MKDEV(dev_major, 0), 1);
    device_create(mychardev_class, NULL, MKDEV(dev_major, 0), NULL, "fpgamem");

    return 0;
}

static void __exit enzian_memory_exit(void)
{
    device_destroy(mychardev_class, MKDEV(dev_major, 0));
    class_destroy(mychardev_class);
    unregister_chrdev_region(MKDEV(dev_major, 0), MINORMASK);
}

module_init(enzian_memory_init);
module_exit(enzian_memory_exit);
