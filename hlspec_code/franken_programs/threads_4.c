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

#include <threads.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdbool.h>
#include "mmap_userspace.h"

void * const addr = (void *) MY_MMAP_ADDRESS_RANGE_START;
sem_t sem;

int mythread(void* thr_data) {
  long n = (long) thr_data;
  sem_wait(&sem);
  long* const numbers = (long * const) addr;
  long* const number = numbers + (n - 1);
  *number = n;
  return 0;
}

int main(void) {
  if (open_mmap_fd()) {
      printf("failed to initialize the mmap subsystem\n");
      return -1;
  }

  unsigned long thr_count = 4;
  thrd_t thr[thr_count];
  sem_init(&sem, 0, 0);
  for(long n = 0; n < thr_count; ++n)
      thrd_create(&thr[n], mythread, (void *) (n + 1));
  // void* alloc = (long*) mmap((void *) addr, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  void* alloc = my_mmap((void *)MY_MMAP_ADDRESS_RANGE_START, BASE_PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_ANONYMOUS, -1, 0);
  if (alloc == MAP_FAILED) {
    return 1;
  }
  for(long n = 0; n < thr_count; ++n)
      sem_post(&sem);
  for(long n = 0; n < thr_count; ++n)
      thrd_join(thr[n], NULL);
  long* numbers = (long*) addr;
  long sum = 0;
  for(long n = 0; n < thr_count; ++n)
      sum += numbers[n];
  printf("%ld\n", sum); // assert(sum == 10);
}

//
