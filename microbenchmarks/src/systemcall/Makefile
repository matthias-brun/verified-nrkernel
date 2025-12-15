
LINUX_PATH=../../../linux
LINUX_MODULE_PATH=$(LINUX_PATH)/module
INC_MODULE=$(LINUX_PATH)/include

CFILES=bench.c
INC=-I$(INC_MODULE)
ARCHIVES=

all: bench

bench: $(CFILES) $(ARCHIVES)
	gcc -O3 -o bench $(INC) $(CFILES) $(ARCHIVES)

clean:
	rm -rf bench

run: bench
	./bench
