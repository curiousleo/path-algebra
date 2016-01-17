all: deps llncs .dir-locals.el

deps:
	git submodule update --init

.dir-locals.el:
	@echo "((agda2-mode" > $@
	@echo " (agda2-include-dirs \".\" \"$(CURDIR)/src\" \"$(CURDIR)/lib/agda-stdlib/src\" \"$(CURDIR)/src\")))" >> $@

llncs:
	$(MAKE) -C pub llncs

.PHONY: all deps
