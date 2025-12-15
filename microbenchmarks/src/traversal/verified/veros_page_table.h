
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

#include<stdint.h>
#include<stdbool.h>
#include<sys/mman.h>

// from the verified code interface!
struct Flags {
    bool is_writable;
    bool is_supervisor;
    bool disable_execute;
};

struct MemRegionExec {
    uint64_t base;
    uint64_t size;
};

struct PageTableEntryExec {
    struct MemRegionExec frame;
    struct Flags flags;
};



typedef uint64_t paddr_t;

int64_t veros_map_frame(uint64_t pml4, uint64_t vaddr, struct PageTableEntryExec *pte);
int64_t veros_unmap_frame(uint64_t pml4, uint64_t vaddr, struct MemRegionExec *ret_frame);


