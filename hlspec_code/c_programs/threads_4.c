#include <threads.h>
#include <sys/mman.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdbool.h>

void * const addr = (void *) (512UL << 30);
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
  unsigned long thr_count = 4;
  thrd_t thr[thr_count];
  sem_init(&sem, 0, 0);
  for(long n = 0; n < thr_count; ++n)
      thrd_create(&thr[n], mythread, (void *) (n + 1));
  void* alloc = (long*) mmap((void *) addr, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
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
