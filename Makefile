all: deps .dir-locals.el sub/llncs.cls

deps:
	git submodule update --init

.dir-locals.el:
	@echo "((agda2-mode" > $@
	@echo " (agda2-include-dirs \".\" \"$(CURDIR)/lib/agda-stdlib/src\" \"$(CURDIR)/src\")))" >> $@

sub/llncs.cls:
	$(MAKE) -C pub llncs.cls

.PHONY: all deps
