#ifndef __VERIFIED_MMAP_IOCTL_H__
#define __VERIFIED_MMAP_IOCTL_H__

#define VA_RANGE_MIN (16UL * (512ULL << 30))
#define VA_RANGE_MAX (17UL * (512ULL << 30))

// arguments

struct mmap_args {
    uint64_t vaddr;
    uint64_t sz;
    uint64_t flags;
};

struct mprotect_args {
    uint64_t vaddr;
    uint64_t sz;
    uint64_t flags;
};

struct munmap_args {
    uint64_t vaddr;
    uint64_t sz;
};

union verified_mmap_ioctl_args {
    struct mmap_args mmap_args;
    struct mprotect_args mprotect_args;
    struct munmap_args munmap_args;
};

// commands
#define CMD_MMAP        _IOW('q', 1, union verified_mmap_ioctl_args*)
#define CMD_MPROTECT    _IOW('q', 2, union verified_mmap_ioctl_args*)
#define CMD_MUNMAP      _IOW('q', 3, union verified_mmap_ioctl_args*)

#endif