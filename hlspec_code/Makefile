

all: map_unmap_fault threads_4 two_threads_map

run: all mmap_mod_verified.ko
	@echo "\nInstalling module"
	sudo insmod mmap_mod_verified.ko
	@echo "\nRunning two_threads_map:"
	./two_threads_map
	@echo "\nRunning threads_4:"
	./threads_4
	@echo "\nRunning map_unmap_fault (expecting segfault, may take a little while.)"
	./map_unmap_fault || true
	@echo "\nUnloading module."
	sudo rmmod mmap_mod_verified.ko
	@echo "Done."




map_unmap_fault: franken_programs/map_unmap_fault.c
	gcc $(CFLAGS) -o $@ $<

threads_4: franken_programs/threads_4.c
	gcc $(CFLAGS) -o $@ $<

two_threads_map: franken_programs/two_threads_map.c
	gcc $(CFLAGS) -o $@ $<

mmap_mod_verified.ko:
	IMPL=verified $(MAKE) -C ../linux/module
	cp ../linux/module/mmap_mod_verified.ko $@