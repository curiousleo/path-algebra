.dir-locals.el:
	@echo "((agda2-mode" > $@
	@echo " (agda2-include-dirs \".\" \"$(CURDIR)/lib/agda-stdlib/src\" \"$(CURDIR)/src\")))" >> $@
