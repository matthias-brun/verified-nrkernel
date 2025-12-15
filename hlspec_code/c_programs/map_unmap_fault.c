#include <threads.h>
#include <sys/mman.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdbool.h>

void * const addr = (void *) (512UL << 30);

int main(void) {
  void* alloc = (long*) mmap((void *) addr, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (alloc == MAP_FAILED) {
    return 1;
  }
  if (munmap(alloc, 4096) == -1) {
    return 1;
  }

  long* v = (long*) addr;
  *v = 10;
  printf("%ld\n", *v);
}

// 
