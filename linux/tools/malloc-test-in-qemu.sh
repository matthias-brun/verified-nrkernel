

# make sure all logs appear on the console
dmesg -wH &

sleep 2

# insert the module and unload it
insmod module/verified_mmap.ko
rmmod module/verified_mmap.ko

# insert the module again.
insmod module/verified_mmap.ko

# disable randomization
echo 0 | sudo tee /proc/sys/kernel/randomize_va_space

# execute the test
./user/verified_mmap_test

# execute the test
(cd user && LD_PRELOAD="$(pwd)/libjemalloc.so" ./malloc_test)
(cd user && ./malloc_test_static)

killall dmesg

sleep 5

(cd user && LD_PRELOAD="$(pwd)/libjemalloc.so" ./malloc_test)
(cd user && ./malloc_test_static)
