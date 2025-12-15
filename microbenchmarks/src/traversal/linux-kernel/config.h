#ifndef __CONFIG__
#define __CONFIG__

#include <assert.h>

#define CONFIG_PGTABLE_LEVELS 4
#define CONFIG_X86_64
#define CONFIG_MMU
#define CONFIG_64BIT
#define CONFIG_PAGE_SHIFT 12
#define CONFIG_PHYS_ADDR_T_64BIT
// #define CONFIG_SMP 1
#define CONFIG_FLATMEM

#define __KERNEL__

#ifndef __READ_ONCE
#define __READ_ONCE(x)	(*(const volatile typeof(x) *)&(x))
#endif

#define READ_ONCE(x)							\
({									\
	__READ_ONCE(x);							\
})

#define __WRITE_ONCE(x, val)						\
do {									\
	*(volatile typeof(x) *)&(x) = (val);				\
} while (0)

#define WRITE_ONCE(x, val)						\
do {									\
	__WRITE_ONCE(x, val);						\
} while (0)

#include<asm/cmpxchg.h>

#define try_cmpxchg(ptr, pold, new) arch_try_cmpxchg(ptr, pold, new)

#define unlikely(x) x
#define likely(x) x

#define panic(x) assert(!x)

typedef int spinlock_t;


typedef void nodemask_t;

struct page {
   unsigned long addr;
};

#define page_to_pfn(page) ((page->addr) >> PAGE_SHIFT)


#endif