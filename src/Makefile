include ../agda.mk

check: Everything.agda
	$(AGDA) $(AFLAGS) Everything.agda

Everything.agda:
	echo "module Everything where" > $@
	../bin/everything.sh > $@

.PHONY: check
