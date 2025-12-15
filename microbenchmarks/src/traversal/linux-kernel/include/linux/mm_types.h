/* SPDX-License-Identifier: GPL-2.0 */
#ifndef _LINUX_MM_TYPES_H
#define _LINUX_MM_TYPES_H

#include <asm/pgtable_types.h>


/*
 * A swap entry has to fit into a "unsigned long", as the entry is hidden
 * in the "index" field of the swapper address space.
 */
typedef struct {
	unsigned long val;
} swp_entry_t;


/**
 * struct ptdesc -    Memory descriptor for page tables.
 * @__page_flags:     Same as page flags. Powerpc only.
 * @pt_rcu_head:      For freeing page table pages.
 * @pt_list:          List of used page tables. Used for s390 and x86.
 * @_pt_pad_1:        Padding that aliases with page's compound head.
 * @pmd_huge_pte:     Protected by ptdesc->ptl, used for THPs.
 * @__page_mapping:   Aliases with page->mapping. Unused for page tables.
 * @pt_index:         Used for s390 gmap.
 * @pt_mm:            Used for x86 pgds.
 * @pt_frag_refcount: For fragmented page table tracking. Powerpc only.
 * @_pt_pad_2:        Padding to ensure proper alignment.
 * @ptl:              Lock for the page table.
 * @__page_type:      Same as page->page_type. Unused for page tables.
 * @__page_refcount:  Same as page refcount.
 * @pt_memcg_data:    Memcg data. Tracked for page tables here.
 *
 * This struct overlays struct page for now. Do not modify without a good
 * understanding of the issues.
 */
struct ptdesc {
	unsigned long __page_flags;

	union {
		// struct rcu_head pt_rcu_head;
		struct list_head pt_list;
		struct {
			unsigned long _pt_pad_1;
			pgtable_t pmd_huge_pte;
		};
	};
	unsigned long __page_mapping;

	union {
		pgoff_t pt_index;
		struct mm_struct *pt_mm;
		atomic_t pt_frag_refcount;
	};

	union {
		unsigned long _pt_pad_2;
#if ALLOC_SPLIT_PTLOCKS
		spinlock_t *ptl;
#else
		spinlock_t ptl;
#endif
	};
	unsigned int __page_type;
	atomic_t __page_refcount;
#ifdef CONFIG_MEMCG
	unsigned long pt_memcg_data;
#endif
};




// #define ptdesc_page(pt)			(_Generic((pt),			\
// 	const struct ptdesc *:		(const struct page *)(pt),	\
// 	struct ptdesc *:		(struct page *)(pt)))

// #define ptdesc_folio(pt)		(_Generic((pt),			\
// 	const struct ptdesc *:		(const struct folio *)(pt),	\
// 	struct ptdesc *:		(struct folio *)(pt)))

// #define page_ptdesc(p)			(_Generic((p),			\
// 	const struct page *:		(const struct ptdesc *)(p),	\
// 	struct page *:			(struct ptdesc *)(p)))



typedef unsigned long vm_flags_t;

/*
 * A region containing a mapping of a non-memory backed file under NOMMU
 * conditions.  These are held in a global tree and are pinned by the VMAs that
 * map parts of them.
 */
struct vm_region {
	// struct rb_node	vm_rb;		/* link in global region tree */
	vm_flags_t	vm_flags;	/* VMA vm_flags */
	unsigned long	vm_start;	/* start address of region */
	unsigned long	vm_end;		/* region initialised to here */
	unsigned long	vm_top;		/* region allocated to here */
	unsigned long	vm_pgoff;	/* the offset in vm_file corresponding to vm_start */
	// struct file	*vm_file;	/* the backing file or NULL */

	int		vm_usage;	/* region usage count (access under nommu_region_sem) */
	bool		vm_icache_flushed : 1; /* true if the icache has been flushed for
						* this region */
};

/**
 * typedef vm_fault_t - Return type for page fault handlers.
 *
 * Page fault handlers return a bitmask of %VM_FAULT values.
 */
typedef unsigned int vm_fault_t;

enum vm_fault_reason {
	VM_FAULT_OOM            = 0x000001,
	VM_FAULT_SIGBUS         = 0x000002,
	VM_FAULT_MAJOR          = 0x000004,
	VM_FAULT_HWPOISON       = 0x000010,
	VM_FAULT_HWPOISON_LARGE = 0x000020,
	VM_FAULT_SIGSEGV        = 0x000040,
	VM_FAULT_NOPAGE         = 0x000100,
	VM_FAULT_LOCKED         = 0x000200,
	VM_FAULT_RETRY          = 0x000400,
	VM_FAULT_FALLBACK       = 0x000800,
	VM_FAULT_DONE_COW       = 0x001000,
	VM_FAULT_NEEDDSYNC      = 0x002000,
	VM_FAULT_COMPLETED      = 0x004000,
	VM_FAULT_HINDEX_MASK    = 0x0f0000,
};

enum fault_flag {
	FAULT_FLAG_WRITE =		1 << 0,
	FAULT_FLAG_MKWRITE =		1 << 1,
	FAULT_FLAG_ALLOW_RETRY =	1 << 2,
	FAULT_FLAG_RETRY_NOWAIT = 	1 << 3,
	FAULT_FLAG_KILLABLE =		1 << 4,
	FAULT_FLAG_TRIED = 		1 << 5,
	FAULT_FLAG_USER =		1 << 6,
	FAULT_FLAG_REMOTE =		1 << 7,
	FAULT_FLAG_INSTRUCTION =	1 << 8,
	FAULT_FLAG_INTERRUPTIBLE =	1 << 9,
	FAULT_FLAG_UNSHARE =		1 << 10,
	FAULT_FLAG_ORIG_PTE_VALID =	1 << 11,
	FAULT_FLAG_VMA_LOCK =		1 << 12,
};

/*
 * vm_flags in vm_area_struct, see mm_types.h.
 * When changing, update also include/trace/events/mmflags.h
 */
#define VM_NONE		0x00000000

#define VM_READ		0x00000001	/* currently active flags */
#define VM_WRITE	0x00000002
#define VM_EXEC		0x00000004
#define VM_SHARED	0x00000008

/* mprotect() hardcodes VM_MAYREAD >> 4 == VM_READ, and so for r/w/x bits. */
#define VM_MAYREAD	0x00000010	/* limits for mprotect() etc */
#define VM_MAYWRITE	0x00000020
#define VM_MAYEXEC	0x00000040
#define VM_MAYSHARE	0x00000080

#define VM_GROWSDOWN	0x00000100	/* general info on the segment */
#ifdef CONFIG_MMU
#define VM_UFFD_MISSING	0x00000200	/* missing pages tracking */
#else /* CONFIG_MMU */
#define VM_MAYOVERLAY	0x00000200	/* nommu: R/O MAP_PRIVATE mapping that might overlay a file mapping */
#define VM_UFFD_MISSING	0
#endif /* CONFIG_MMU */
#define VM_PFNMAP	0x00000400	/* Page-ranges managed without "struct page", just pure PFN */
#define VM_UFFD_WP	0x00001000	/* wrprotect pages tracking */

#define VM_LOCKED	0x00002000
#define VM_IO           0x00004000	/* Memory mapped I/O or similar */

					/* Used by sys_madvise() */
#define VM_SEQ_READ	0x00008000	/* App will access data sequentially */
#define VM_RAND_READ	0x00010000	/* App will not benefit from clustered reads */

#define VM_DONTCOPY	0x00020000      /* Do not copy this vma on fork */
#define VM_DONTEXPAND	0x00040000	/* Cannot expand with mremap() */
#define VM_LOCKONFAULT	0x00080000	/* Lock the pages covered when they are faulted in */
#define VM_ACCOUNT	0x00100000	/* Is a VM accounted object */
#define VM_NORESERVE	0x00200000	/* should the VM suppress accounting */
#define VM_HUGETLB	0x00400000	/* Huge TLB Page VM */
#define VM_SYNC		0x00800000	/* Synchronous page faults */
#define VM_ARCH_1	0x01000000	/* Architecture-specific flag */
#define VM_WIPEONFORK	0x02000000	/* Wipe VMA contents in child. */
#define VM_DONTDUMP	0x04000000	/* Do not include in the core dump */

#ifdef CONFIG_MEM_SOFT_DIRTY
# define VM_SOFTDIRTY	0x08000000	/* Not soft dirty clean area */
#else
# define VM_SOFTDIRTY	0
#endif

#define VM_MIXEDMAP	0x10000000	/* Can contain "struct page" and pure PFN pages */
#define VM_HUGEPAGE	0x20000000	/* MADV_HUGEPAGE marked this vma */
#define VM_NOHUGEPAGE	0x40000000	/* MADV_NOHUGEPAGE marked this vma */
#define VM_MERGEABLE	0x80000000	/* KSM may merge identical pages */

#ifdef CONFIG_ARCH_USES_HIGH_VMA_FLAGS
#define VM_HIGH_ARCH_BIT_0	32	/* bit only usable on 64-bit architectures */
#define VM_HIGH_ARCH_BIT_1	33	/* bit only usable on 64-bit architectures */
#define VM_HIGH_ARCH_BIT_2	34	/* bit only usable on 64-bit architectures */
#define VM_HIGH_ARCH_BIT_3	35	/* bit only usable on 64-bit architectures */
#define VM_HIGH_ARCH_BIT_4	36	/* bit only usable on 64-bit architectures */
#define VM_HIGH_ARCH_BIT_5	37	/* bit only usable on 64-bit architectures */
#define VM_HIGH_ARCH_0	BIT(VM_HIGH_ARCH_BIT_0)
#define VM_HIGH_ARCH_1	BIT(VM_HIGH_ARCH_BIT_1)
#define VM_HIGH_ARCH_2	BIT(VM_HIGH_ARCH_BIT_2)
#define VM_HIGH_ARCH_3	BIT(VM_HIGH_ARCH_BIT_3)
#define VM_HIGH_ARCH_4	BIT(VM_HIGH_ARCH_BIT_4)
#define VM_HIGH_ARCH_5	BIT(VM_HIGH_ARCH_BIT_5)
#endif /* CONFIG_ARCH_USES_HIGH_VMA_FLAGS */

#ifdef CONFIG_ARCH_HAS_PKEYS
# define VM_PKEY_SHIFT	VM_HIGH_ARCH_BIT_0
# define VM_PKEY_BIT0	VM_HIGH_ARCH_0	/* A protection key is a 4-bit value */
# define VM_PKEY_BIT1	VM_HIGH_ARCH_1	/* on x86 and 5-bit value on ppc64   */
# define VM_PKEY_BIT2	VM_HIGH_ARCH_2
# define VM_PKEY_BIT3	VM_HIGH_ARCH_3
#ifdef CONFIG_PPC
# define VM_PKEY_BIT4  VM_HIGH_ARCH_4
#else
# define VM_PKEY_BIT4  0
#endif
#endif /* CONFIG_ARCH_HAS_PKEYS */

#ifdef CONFIG_X86_USER_SHADOW_STACK
/*
 * VM_SHADOW_STACK should not be set with VM_SHARED because of lack of
 * support core mm.
 *
 * These VMAs will get a single end guard page. This helps userspace protect
 * itself from attacks. A single page is enough for current shadow stack archs
 * (x86). See the comments near alloc_shstk() in arch/x86/kernel/shstk.c
 * for more details on the guard size.
 */
# define VM_SHADOW_STACK	VM_HIGH_ARCH_5
#else
# define VM_SHADOW_STACK	VM_NONE
#endif

#if defined(CONFIG_X86)
# define VM_PAT		VM_ARCH_1	/* PAT reserves whole VMA at once (x86) */
#elif defined(CONFIG_PPC)
# define VM_SAO		VM_ARCH_1	/* Strong Access Ordering (powerpc) */
#elif defined(CONFIG_PARISC)
# define VM_GROWSUP	VM_ARCH_1
#elif defined(CONFIG_SPARC64)
# define VM_SPARC_ADI	VM_ARCH_1	/* Uses ADI tag for access control */
# define VM_ARCH_CLEAR	VM_SPARC_ADI
#elif defined(CONFIG_ARM64)
# define VM_ARM64_BTI	VM_ARCH_1	/* BTI guarded page, a.k.a. GP bit */
# define VM_ARCH_CLEAR	VM_ARM64_BTI
#elif !defined(CONFIG_MMU)
# define VM_MAPPED_COPY	VM_ARCH_1	/* T if mapped copy of data (nommu mmap) */
#endif

#if defined(CONFIG_ARM64_MTE)
# define VM_MTE		VM_HIGH_ARCH_0	/* Use Tagged memory for access control */
# define VM_MTE_ALLOWED	VM_HIGH_ARCH_1	/* Tagged memory permitted */
#else
# define VM_MTE		VM_NONE
# define VM_MTE_ALLOWED	VM_NONE
#endif

#ifndef VM_GROWSUP
# define VM_GROWSUP	VM_NONE
#endif

#ifdef CONFIG_HAVE_ARCH_USERFAULTFD_MINOR
# define VM_UFFD_MINOR_BIT	38
# define VM_UFFD_MINOR		BIT(VM_UFFD_MINOR_BIT)	/* UFFD minor faults */
#else /* !CONFIG_HAVE_ARCH_USERFAULTFD_MINOR */
# define VM_UFFD_MINOR		VM_NONE
#endif /* CONFIG_HAVE_ARCH_USERFAULTFD_MINOR */

/*
 * This flag is used to connect VFIO to arch specific KVM code. It
 * indicates that the memory under this VMA is safe for use with any
 * non-cachable memory type inside KVM. Some VFIO devices, on some
 * platforms, are thought to be unsafe and can cause machine crashes
 * if KVM does not lock down the memory type.
 */
#ifdef CONFIG_64BIT
#define VM_ALLOW_ANY_UNCACHED_BIT	39
#define VM_ALLOW_ANY_UNCACHED		BIT(VM_ALLOW_ANY_UNCACHED_BIT)
#else
#define VM_ALLOW_ANY_UNCACHED		VM_NONE
#endif

/* Bits set in the VMA until the stack is in its final location */
#define VM_STACK_INCOMPLETE_SETUP (VM_RAND_READ | VM_SEQ_READ | VM_STACK_EARLY)

#define TASK_EXEC ((current->personality & READ_IMPLIES_EXEC) ? VM_EXEC : 0)

/* Common data flag combinations */
#define VM_DATA_FLAGS_TSK_EXEC	(VM_READ | VM_WRITE | TASK_EXEC | \
				 VM_MAYREAD | VM_MAYWRITE | VM_MAYEXEC)
#define VM_DATA_FLAGS_NON_EXEC	(VM_READ | VM_WRITE | VM_MAYREAD | \
				 VM_MAYWRITE | VM_MAYEXEC)
#define VM_DATA_FLAGS_EXEC	(VM_READ | VM_WRITE | VM_EXEC | \
				 VM_MAYREAD | VM_MAYWRITE | VM_MAYEXEC)

#ifndef VM_DATA_DEFAULT_FLAGS		/* arch can override this */
#define VM_DATA_DEFAULT_FLAGS  VM_DATA_FLAGS_EXEC
#endif

#ifndef VM_STACK_DEFAULT_FLAGS		/* arch can override this */
#define VM_STACK_DEFAULT_FLAGS VM_DATA_DEFAULT_FLAGS
#endif

#define VM_STARTGAP_FLAGS (VM_GROWSDOWN | VM_SHADOW_STACK)

#ifdef CONFIG_STACK_GROWSUP
#define VM_STACK	VM_GROWSUP
#define VM_STACK_EARLY	VM_GROWSDOWN
#else
#define VM_STACK	VM_GROWSDOWN
#define VM_STACK_EARLY	0
#endif

#define VM_STACK_FLAGS	(VM_STACK | VM_STACK_DEFAULT_FLAGS | VM_ACCOUNT)

/* VMA basic access permission flags */
#define VM_ACCESS_FLAGS (VM_READ | VM_WRITE | VM_EXEC)


/*
 * Special vmas that are non-mergable, non-mlock()able.
 */
#define VM_SPECIAL (VM_IO | VM_DONTEXPAND | VM_PFNMAP | VM_MIXEDMAP)

/* This mask prevents VMA from being scanned with khugepaged */
#define VM_NO_KHUGEPAGED (VM_SPECIAL | VM_HUGETLB)

/* This mask defines which mm->def_flags a process can inherit its parent */
#define VM_INIT_DEF_MASK	VM_NOHUGEPAGE

/* This mask represents all the VMA flag bits used by mlock */
#define VM_LOCKED_MASK	(VM_LOCKED | VM_LOCKONFAULT)

/* Arch-specific flags to clear when updating VM flags on protection change */
#ifndef VM_ARCH_CLEAR
# define VM_ARCH_CLEAR	VM_NONE
#endif
#define VM_FLAGS_CLEAR	(ARCH_VM_PKEY_FLAGS | VM_ARCH_CLEAR)

/*
 * mapping from the currently active vm_flags protection bits (the
 * low four bits) to a page protection mask..
 */

/*
 * The default fault flags that should be used by most of the
 * arch-specific page fault handlers.
 */
#define FAULT_FLAG_DEFAULT  (FAULT_FLAG_ALLOW_RETRY | \
			     FAULT_FLAG_KILLABLE | \
			     FAULT_FLAG_INTERRUPTIBLE)

typedef unsigned long vm_flags_t;

/*
 * This struct describes a virtual memory area. There is one of these
 * per VM-area/task. A VM area is any part of the process virtual memory
 * space that has a special rule for the page-fault handlers (ie a shared
 * library, the executable area etc).
 */
struct vm_area_struct {
	/* The first cache line has the info for VMA tree walking. */

	union {
		struct {
			/* VMA covers [vm_start; vm_end) addresses within mm */
			unsigned long vm_start;
			unsigned long vm_end;
		};
#ifdef CONFIG_PER_VMA_LOCK
		struct rcu_head vm_rcu;	/* Used for deferred freeing. */
#endif
	};

	struct mm_struct *vm_mm;	/* The address space we belong to. */
	pgprot_t vm_page_prot;          /* Access permissions of this VMA. */

	/*
	 * Flags, see mm.h.
	 * To modify use vm_flags_{init|reset|set|clear|mod} functions.
	 */
	union {
		const vm_flags_t vm_flags;
		vm_flags_t __vm_flags;
	};

#ifdef CONFIG_PER_VMA_LOCK
	/* Flag to indicate areas detached from the mm->mm_mt tree */
	bool detached;

	/*
	 * Can only be written (using WRITE_ONCE()) while holding both:
	 *  - mmap_lock (in write mode)
	 *  - vm_lock->lock (in write mode)
	 * Can be read reliably while holding one of:
	 *  - mmap_lock (in read or write mode)
	 *  - vm_lock->lock (in read or write mode)
	 * Can be read unreliably (using READ_ONCE()) for pessimistic bailout
	 * while holding nothing (except RCU to keep the VMA struct allocated).
	 *
	 * This sequence counter is explicitly allowed to overflow; sequence
	 * counter reuse can only lead to occasional unnecessary use of the
	 * slowpath.
	 */
	int vm_lock_seq;
	struct vma_lock *vm_lock;
#endif

	/*
	 * For areas with an address space and backing store,
	 * linkage into the address_space->i_mmap interval tree.
	 *
	 */
	// struct {
	// 	struct rb_node rb;
	// 	unsigned long rb_subtree_last;
	// } shared;

	/*
	 * A file's MAP_PRIVATE vma can be in both i_mmap tree and anon_vma
	 * list, after a COW of one of the file pages.	A MAP_SHARED vma
	 * can only be in the i_mmap tree.  An anonymous MAP_PRIVATE, stack
	 * or brk vma (with NULL file) can only be in an anon_vma list.
	 */
	struct list_head anon_vma_chain; /* Serialized by mmap_lock &
					  * page_table_lock */
	struct anon_vma *anon_vma;	/* Serialized by page_table_lock */

	/* Function pointers to deal with this struct. */
	const struct vm_operations_struct *vm_ops;

	/* Information about our backing store: */
	unsigned long vm_pgoff;		/* Offset (within vm_file) in PAGE_SIZE
					   units */
	struct file * vm_file;		/* File we map to (can be NULL). */
	void * vm_private_data;		/* was vm_pte (shared mem) */

#ifdef CONFIG_ANON_VMA_NAME
	/*
	 * For private and shared anonymous mappings, a pointer to a null
	 * terminated string containing the name given to the vma, or NULL if
	 * unnamed. Serialized by mmap_lock. Use anon_vma_name to access.
	 */
	struct anon_vma_name *anon_name;
#endif
#ifdef CONFIG_SWAP
	atomic_long_t swap_readahead_info;
#endif
#ifndef CONFIG_MMU
	struct vm_region *vm_region;	/* NOMMU mapping region */
#endif
#ifdef CONFIG_NUMA
	struct mempolicy *vm_policy;	/* NUMA policy for the VMA */
#endif
#ifdef CONFIG_NUMA_BALANCING
	struct vma_numab_state *numab_state;	/* NUMA Balancing state */
#endif
	// struct vm_userfaultfd_ctx vm_userfaultfd_ctx;
};


struct kioctx_table;
struct iommu_mm_data;
struct mm_struct {
	struct {
		/*
		 * Fields which are often written to are placed in a separate
		 * cache line.
		 */
		struct {
			/**
			 * @mm_count: The number of references to &struct
			 * mm_struct (@mm_users count as 1).
			 *
			 * Use mmgrab()/mmdrop() to modify. When this drops to
			 * 0, the &struct mm_struct is freed.
			 */
			atomic_t mm_count;
		} ____cacheline_aligned_in_smp;

		// struct maple_tree mm_mt;

		unsigned long mmap_base;	/* base of mmap area */
		unsigned long mmap_legacy_base;	/* base of mmap area in bottom-up allocations */
#ifdef CONFIG_HAVE_ARCH_COMPAT_MMAP_BASES
		/* Base addresses for compatible mmap() */
		unsigned long mmap_compat_base;
		unsigned long mmap_compat_legacy_base;
#endif
		unsigned long task_size;	/* size of task vm space */
		pgd_t * pgd;

#ifdef CONFIG_MEMBARRIER
		/**
		 * @membarrier_state: Flags controlling membarrier behavior.
		 *
		 * This field is close to @pgd to hopefully fit in the same
		 * cache-line, which needs to be touched by switch_mm().
		 */
		atomic_t membarrier_state;
#endif

		/**
		 * @mm_users: The number of users including userspace.
		 *
		 * Use mmget()/mmget_not_zero()/mmput() to modify. When this
		 * drops to 0 (i.e. when the task exits and there are no other
		 * temporary reference holders), we also release a reference on
		 * @mm_count (which may then free the &struct mm_struct if
		 * @mm_count also drops to 0).
		 */
		atomic_t mm_users;

#ifdef CONFIG_SCHED_MM_CID
		/**
		 * @pcpu_cid: Per-cpu current cid.
		 *
		 * Keep track of the currently allocated mm_cid for each cpu.
		 * The per-cpu mm_cid values are serialized by their respective
		 * runqueue locks.
		 */
		struct mm_cid __percpu *pcpu_cid;
		/*
		 * @mm_cid_next_scan: Next mm_cid scan (in jiffies).
		 *
		 * When the next mm_cid scan is due (in jiffies).
		 */
		unsigned long mm_cid_next_scan;
#endif
#ifdef CONFIG_MMU
		atomic_long_t pgtables_bytes;	/* size of all page tables */
#endif
		int map_count;			/* number of VMAs */

		// spinlock_t page_table_lock; /* Protects page tables and some
					    //  * counters
					    //  */
		/*
		 * With some kernel config, the current mmap_lock's offset
		 * inside 'mm_struct' is at 0x120, which is very optimal, as
		 * its two hot fields 'count' and 'owner' sit in 2 different
		 * cachelines,  and when mmap_lock is highly contended, both
		 * of the 2 fields will be accessed frequently, current layout
		 * will help to reduce cache bouncing.
		 *
		 * So please be careful with adding new fields before
		 * mmap_lock, which can easily push the 2 fields into one
		 * cacheline.
		 */
		// struct rw_semaphore mmap_lock;

		struct list_head mmlist; /* List of maybe swapped mm's.	These
					  * are globally strung together off
					  * init_mm.mmlist, and are protected
					  * by mmlist_lock
					  */
#ifdef CONFIG_PER_VMA_LOCK
		/*
		 * This field has lock-like semantics, meaning it is sometimes
		 * accessed with ACQUIRE/RELEASE semantics.
		 * Roughly speaking, incrementing the sequence number is
		 * equivalent to releasing locks on VMAs; reading the sequence
		 * number can be part of taking a read lock on a VMA.
		 *
		 * Can be modified under write mmap_lock using RELEASE
		 * semantics.
		 * Can be read with no other protection when holding write
		 * mmap_lock.
		 * Can be read with ACQUIRE semantics if not holding write
		 * mmap_lock.
		 */
		int mm_lock_seq;
#endif


		unsigned long hiwater_rss; /* High-watermark of RSS usage */
		unsigned long hiwater_vm;  /* High-water virtual memory usage */

		unsigned long total_vm;	   /* Total pages mapped */
		unsigned long locked_vm;   /* Pages that have PG_mlocked set */
		atomic64_t    pinned_vm;   /* Refcount permanently increased */
		unsigned long data_vm;	   /* VM_WRITE & ~VM_SHARED & ~VM_STACK */
		unsigned long exec_vm;	   /* VM_EXEC & ~VM_WRITE & ~VM_STACK */
		unsigned long stack_vm;	   /* VM_STACK */
		unsigned long def_flags;

		/**
		 * @write_protect_seq: Locked when any thread is write
		 * protecting pages mapped by this mm to enforce a later COW,
		 * for instance during page table copying for fork().
		 */
		// seqcount_t write_protect_seq;

		// spinlock_t arg_lock; /* protect the below fields */

		unsigned long start_code, end_code, start_data, end_data;
		unsigned long start_brk, brk, start_stack;
		unsigned long arg_start, arg_end, env_start, env_end;

		// unsigned long saved_auxv[AT_VECTOR_SIZE]; /* for /proc/PID/auxv */

		// struct percpu_counter rss_stat[NR_MM_COUNTERS];

		struct linux_binfmt *binfmt;

		/* Architecture-specific MM context */
		// mm_context_t context;

		unsigned long flags; /* Must use atomic bitops to access */

#ifdef CONFIG_AIO
		spinlock_t			ioctx_lock;
		struct kioctx_table __rcu	*ioctx_table;
#endif
#ifdef CONFIG_MEMCG
		/*
		 * "owner" points to a task that is regarded as the canonical
		 * user/owner of this mm. All of the following must be true in
		 * order for it to be changed:
		 *
		 * current == mm->owner
		 * current->mm != mm
		 * new_owner->mm == mm
		 * new_owner->alloc_lock is held
		 */
		struct task_struct __rcu *owner;
#endif
		struct user_namespace *user_ns;

		/* store ref to file /proc/<pid>/exe symlink points to */
		// struct file __rcu *exe_file;
#ifdef CONFIG_MMU_NOTIFIER
		struct mmu_notifier_subscriptions *notifier_subscriptions;
#endif
#if defined(CONFIG_TRANSPARENT_HUGEPAGE) && !USE_SPLIT_PMD_PTLOCKS
		pgtable_t pmd_huge_pte; /* protected by page_table_lock */
#endif
#ifdef CONFIG_NUMA_BALANCING
		/*
		 * numa_next_scan is the next time that PTEs will be remapped
		 * PROT_NONE to trigger NUMA hinting faults; such faults gather
		 * statistics and migrate pages to new nodes if necessary.
		 */
		unsigned long numa_next_scan;

		/* Restart point for scanning and remapping PTEs. */
		unsigned long numa_scan_offset;

		/* numa_scan_seq prevents two threads remapping PTEs. */
		int numa_scan_seq;
#endif
		/*
		 * An operation with batched TLB flushing is going on. Anything
		 * that can move process memory needs to flush the TLB when
		 * moving a PROT_NONE mapped page.
		 */
		atomic_t tlb_flush_pending;
#ifdef CONFIG_ARCH_WANT_BATCHED_UNMAP_TLB_FLUSH
		/* See flush_tlb_batched_pending() */
		atomic_t tlb_flush_batched;
#endif
		// struct uprobes_state uprobes_state;
#ifdef CONFIG_PREEMPT_RT
		struct rcu_head delayed_drop;
#endif
#ifdef CONFIG_HUGETLB_PAGE
		atomic_long_t hugetlb_usage;
#endif
		// struct work_struct async_put_work;

#ifdef CONFIG_IOMMU_MM_DATA
		struct iommu_mm_data *iommu_mm;
#endif
#ifdef CONFIG_KSM
		/*
		 * Represent how many pages of this process are involved in KSM
		 * merging (not including ksm_zero_pages).
		 */
		unsigned long ksm_merging_pages;
		/*
		 * Represent how many pages are checked for ksm merging
		 * including merged and not merged.
		 */
		unsigned long ksm_rmap_items;
		/*
		 * Represent how many empty pages are merged with kernel zero
		 * pages when enabling KSM use_zero_pages.
		 */
		atomic_long_t ksm_zero_pages;
#endif /* CONFIG_KSM */
#ifdef CONFIG_LRU_GEN_WALKS_MMU
		struct {
			/* this mm_struct is on lru_gen_mm_list */
			struct list_head list;
			/*
			 * Set when switching to this mm_struct, as a hint of
			 * whether it has been used since the last time per-node
			 * page table walkers cleared the corresponding bits.
			 */
			unsigned long bitmap;
#ifdef CONFIG_MEMCG
			/* points to the memcg of "owner" above */
			struct mem_cgroup *memcg;
#endif
		} lru_gen;
#endif /* CONFIG_LRU_GEN_WALKS_MMU */
	} ;

	/*
	 * The mm_cpumask needs to be at the end of mm_struct, because it
	 * is dynamically sized based on nr_cpu_ids.
	 */
	unsigned long cpu_bitmap[];
};


#endif /* _LINUX_MM_TYPES_H */
