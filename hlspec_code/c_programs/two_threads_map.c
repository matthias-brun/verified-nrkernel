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
