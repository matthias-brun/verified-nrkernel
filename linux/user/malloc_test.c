#include <sys/ioctl.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <string.h>
#include <sys/mman.h>

static void test_malloc(size_t bytes) {

	printf("allocating %zu bytes\n", bytes);
    uint64_t *value = malloc(bytes);
	if (value == NULL) {
		printf("malloc failed\n");
		exit(1);
	}

	printf("writing memory...\n");
	*value = 0x12345678;
	printf("Value is =%lx\n", *value);

	printf("freeing memory...\n");
	free(value);
	printf("done.\n");
}

int main (int argc, char **argv)
{
	printf("testing malloc\n");
	// setbuf(stdout, NULL);
	// char buf[BUFSIZ];
	// setbuf(stdout, calloc(1, BUFSIZ));

	// int res = printf("foobar!\n");
	// setbuf(stdout, NULL);
	// printf("res=%d\n", res);

	test_malloc(64);
	test_malloc(1024);
	test_malloc(4096);
	test_malloc(8192);
	test_malloc(2 << 20);
	test_malloc(8 << 20);

}


