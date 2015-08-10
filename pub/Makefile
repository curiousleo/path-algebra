AGDA=agda
AFLAGS=-i../lib/agda-stdlib/src -i../src -i. --latex --latex-dir=.
LATEX=latexmk -pdf

LLNCSZIP=llncs2e.zip

all: itp16.pdf

itp16.pdf: itp16.tex llncs.cls
	$(LATEX) $<

itp16.tex: itp16.lagda
	$(AGDA) $(AFLAGS) $<

llncs.cls:
	@echo "Downloading LLNCS LaTeX package"
	curl -s ftp://ftp.springer.de/pub/tex/latex/llncs/latex2e/llncs2e.zip \
	     -o $(LLNCSZIP)
	unzip -q $(LLNCSZIP) $@
	rm $(LLNCSZIP)

clean:
	rm -f itp16.{tex,aux,fls,log,agdai,fdb_latexmk,pdf,ptb}

purge: clean
	rm -f agda.sty llncs.cls

.PHONY: all clean purge
