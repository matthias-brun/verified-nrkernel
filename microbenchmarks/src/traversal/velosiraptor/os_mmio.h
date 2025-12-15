// Velosiraptor Code Generator
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! MMIO Support Library for the C-Code generation

#ifndef OS_SUPPORT_MMIO_ACCESS_H_
#define OS_SUPPORT_MMIO_ACCESS_H_ 1

#include <stdint.h>

static inline void os_mmio_register_write_8(uintptr_t addr, uintptr_t offset, uint8_t value) {
    *(volatile uint8_t *)(addr + offset) = (uint8_t)value;
}

static inline void os_mmio_register_write_16(uintptr_t addr, uintptr_t offset, uint16_t value) {
    *(volatile uint16_t *)(addr + offset) = (uint16_t)value;
}

static inline void os_mmio_register_write_32(uintptr_t addr, uintptr_t offset, uint32_t value) {
    *(volatile uint32_t *)(addr + offset) = (uint32_t)value;
}

static inline void os_mmio_register_write_64(uintptr_t addr, uintptr_t offset, uint64_t value) {
    *(volatile uint64_t *)(addr + offset) = (uint64_t)value;
}

static inline uint8_t os_mmio_register_read_8(uintptr_t addr, uintptr_t offset) {
    return *(volatile uint8_t *)(addr + offset);
}

static inline uint16_t os_mmio_register_read_16(uintptr_t addr, uintptr_t offset) {
    return *(volatile uint16_t *)(addr + offset);
}

static inline uint32_t os_mmio_register_read_32(uintptr_t addr, uintptr_t offset) {
    return *(volatile uint32_t *)(addr + offset);
}

static inline uint64_t os_mmio_register_read_64(uintptr_t addr, uintptr_t offset) {
    return *(volatile uint64_t *)(addr + offset);
}

#endif // OS_SUPPORT_MMIO_ACCESS_H_