include llncs.mk

LLNCSDEPS = $(patsubst %, pub/%, $(LLNCSFILES))

all: deps .dir-locals.el $(LLNCSDEPS)

deps:
	git submodule update --init

.dir-locals.el:
	@echo "((agda2-mode" > $@
	@echo " (agda2-include-dirs \".\" \"$(CURDIR)/lib/agda-stdlib/src\" \"$(CURDIR)/src\")))" >> $@

$(LLNCSDEPS):
	$(MAKE) -C pub $(patsubst pub/%, %, $@)

.NOTPARALLEL: $(LLNCSDEPS)
.PHONY: all deps
