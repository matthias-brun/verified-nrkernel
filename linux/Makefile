
CFG_IMPL=verified

build:
	make -C user
	(cd module && IMPL=$(CFG_IMPL) make pre)
	(cd module && IMPL=$(CFG_IMPL) make all)

run:
	make -C user
	(cd module && IMPL=$(CFG_IMPL) make all)
	bash tools/qemu-start.sh $(CFG_IMPL)

clean:
	(cd module && make clean)
	(cd user && make clean)

clean_and_run:
	(cd module && make clean)
	(cd module && IMPL=$(CFG_IMPL) make pre)
	(cd module && IMPL=$(CFG_IMPL) make all)
	(cd user && make clean)
	(cd user && make)
	bash tools/qemu-start.sh $(CFG_IMPL)

test:
	bash tools/test-in-qemu.sh $(CFG_IMPL)

pre:
	bash tools/download-linux-image.sh
	make -C module pre
