// MIT License
//
// Copyright (c) 2025 Paper #409 Authors, ASPLOS'26.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

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