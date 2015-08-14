include ../agda.mk

AFLAGS += --latex --latex-dir=.
LATEX = latexmk
LFLAGS = -pdf -silent

LLNCSFILES = llncs.cls splncs03.bst
LLNCSZIP = llncs2e.zip

itp16.pdf: itp16.tex agda.sty llncs
	$(LATEX) $(LFLAGS) $<

itp16.tex: itp16.lagda
	$(AGDA) $(AFLAGS) $<

llncs: $(LLNCSFILES)

$(LLNCSFILES): $(LLNCSZIP)
	unzip -DD -u -q $(LLNCSZIP) $@

$(LLNCSZIP):
	@echo "Downloading LLNCS LaTeX package"
	curl -s ftp://ftp.springer.de/pub/tex/latex/llncs/latex2e/llncs2e.zip \
	     -o $(LLNCSZIP)

clean:
	rm -f itp16.{tex,aux,bbl,blg,fls,log,out,agdai,fdb_latexmk,pdf,ptb}

purge: clean
	rm -f agda.sty $(LLNCSFILES) $(LLNCSZIP)

.PHONY: clean purge
