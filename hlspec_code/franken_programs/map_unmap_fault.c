#include <threads.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdbool.h>
#include "mmap_userspace.h"

void * const addr = (void *) MY_MMAP_ADDRESS_RANGE_START;

int main(void) {
  if (open_mmap_fd()) {
      printf("failed to initialize the mmap subsystem\n");
      return -1;
  }

  // void* alloc = (long*) mmap((void *) addr, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  void* alloc = my_mmap((void *) addr, BASE_PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_ANONYMOUS, -1, 0);
  if (alloc == MAP_FAILED) {
    return 1;
  }
  // if (munmap(alloc, 4096) == -1) {
  if (my_munmap((void *) addr, BASE_PAGE_SIZE) == -1) {
    return 1;
  }

  long* v = (long*) addr;
  *v = 10;
  printf("%ld\n", *v);
}

// 
