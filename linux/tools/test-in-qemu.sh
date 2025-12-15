

# make sure all logs appear on the console
dmesg -wH &

sleep 2

# insert the module and unload it
insmod module/mmap_module.ko
rmmod module/mmap_module.ko

# insert the module again.
insmod module/mmap_module.ko

# execute the test
./user/verified_mmap_test
