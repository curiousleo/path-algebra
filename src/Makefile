include ../agda.mk

check: Everything.agda
	$(AGDA) $(AFLAGS) Everything.agda

Everything.agda:
	../bin/everything.sh > $@

.PHONY: check
