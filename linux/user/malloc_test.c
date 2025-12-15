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


