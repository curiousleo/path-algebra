include ../agda.mk
include ../llncs.mk

AFLAGS += --latex --latex-dir=.
LATEX = latexmk
LFLAGS = -pdf -silent

LLNCSZIP = llncs2e.zip

itp16.pdf: itp16.tex $(LLNCSFILES)
	$(LATEX) $(LFLAGS) $<

itp16.tex: itp16.lagda
	$(AGDA) $(AFLAGS) $<

$(LLNCSFILES): $(LLNCSZIP)
	unzip -DD -u -q $(LLNCSZIP) $@

$(LLNCSZIP):
	@echo "Downloading LLNCS LaTeX package"
	curl -s ftp://ftp.springer.de/pub/tex/latex/llncs/latex2e/llncs2e.zip \
	     -o $(LLNCSZIP)

clean:
	rm -f itp16.{tex,aux,fls,log,agdai,fdb_latexmk,pdf,ptb}

purge: clean
	rm -f agda.sty $(LLNCSFILES) $(LLNCSZIP)

.PHONY: clean purge
