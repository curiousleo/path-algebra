include ../agda.mk

AFLAGS += --latex --latex-dir=.
LATEX = latexmk
LFLAGS = -pdf -silent

LAGDACHAPTERS = $(sort $(wildcard *.lagda))
LAGDATARGETS = $(patsubst %.lagda, %.tex, $(LAGDACHAPTERS))

LLNCSFILES = llncs.cls splncs03.bst
LLNCSZIP = llncs2e.zip

all: itp16.pdf .gitignore

itp16.pdf: itp16.tex $(LAGDATARGETS) agda.sty llncs
	$(LATEX) $(LFLAGS) $<

%.tex: %.lagda
	$(AGDA) $(AFLAGS) $<

llncs: $(LLNCSFILES)

$(LLNCSFILES): $(LLNCSZIP)
	unzip -DD -u -q $(LLNCSZIP) $@

$(LLNCSZIP):
	@echo "Downloading LLNCS LaTeX package"
	curl -s ftp://ftp.springer.de/pub/tex/latex/llncs/latex2e/llncs2e.zip \
	     -o $(LLNCSZIP)

.gitignore:
	echo $(LAGDATARGETS) | tr ' ' '\n' > $@

clean:
	rm -f itp16.{tex,aux,bbl,blg,fls,log,out,agdai,fdb_latexmk,pdf,ptb}

purge: clean
	rm -f agda.sty $(LLNCSFILES) $(LLNCSZIP)

.PHONY: clean purge
