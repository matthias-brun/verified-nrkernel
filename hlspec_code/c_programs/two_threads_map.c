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

// concurrent mapping of disjoint regions
// -- sync --
// once they have completed, access each other pages

#include <threads.h>
#include <sys/mman.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdbool.h>
#include <assert.h>

void * const addr1 = (void *) (512UL << 30);
void * const addr2 = (void *) ((512UL << 30) + 4096);
sem_t sem1;
sem_t sem2;

int mythread_1(void* thr_data) {
  void* alloc = (long*) mmap((void *) addr1, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (alloc == MAP_FAILED) {
    return 1;
  }
  long* const v1 = (long * const) addr1;
  long* const v2 = (long * const) addr2;
  sem_post(&sem2);
  sem_wait(&sem1);
  *v2 = 2;
  sem_post(&sem2);
  sem_wait(&sem1);
  assert(*v1 == 1);
  return 0;
}

int mythread_2(void* thr_data) {
  void* alloc = (long*) mmap((void *) addr2, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (alloc == MAP_FAILED) {
    return 1;
  }
  long* const v1 = (long * const) addr1;
  long* const v2 = (long * const) addr2;
  sem_post(&sem1);
  sem_wait(&sem2);
  *v1 = 1;
  sem_post(&sem1);
  sem_wait(&sem2);
  assert(*v2 == 2);
  return 0;
}

int main(void) {
  thrd_t thr1;
  thrd_t thr2;
  sem_init(&sem1, 0, 0);
  sem_init(&sem2, 0, 0);
  thrd_create(&thr1, mythread_1, (void *) 0);
  thrd_create(&thr2, mythread_2, (void *) 0);
  int t1 = thrd_join(thr1, NULL);
  int t2 = thrd_join(thr2, NULL);
  assert(t1 == 0);
  assert(t2 == 0);
  printf("done\n");
}
