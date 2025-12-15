
INCLUDES = -I../include

all: verified_mmap_test malloc_test malloc_test_static

verified_mmap_test: verified_mmap_test.c
	gcc -o $@ -Wall -O3 $(INCLUDES) $<

malloc_test: malloc_test.c libjemalloc.so
	gcc -o $@ -Wall -O3 -g $(INCLUDES) $<

malloc_test_static: malloc_test.c libjemalloc.so
	gcc -o $@ -Wall -O3 -g -no-pie $(INCLUDES) $<  libjemalloc.a

libjemalloc.so:
	(cd ../jemalloc && make)
	cp ../jemalloc/lib/libjemalloc.so .
	cp ../jemalloc/lib/libjemalloc.a .


clean:
	rm -rf verified_mmap_test
	rm -rf malloc_test
	rm -rf libjemalloc.*

test: verified_mmap_test
	sudo ./verified_mmap_test
