AGDA=agda
AFLAGS=-i../lib/agda-stdlib/src -i. -v 0

check: Everything.agda
	$(AGDA) $(AFLAGS) Everything.agda

Everything.agda:
	echo "module Everything where" > $@
	../bin/everything.sh > $@

.PHONY: check
