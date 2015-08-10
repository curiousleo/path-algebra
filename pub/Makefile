AGDA=agda
AFLAGS=-i../lib/agda-stdlib/src -i../src --latex --latex-dir=. --allow-unsolved-metas
LATEX=latexmk -xelatex

all: itp16.pdf

itp16.pdf: itp16.tex llncs.cls
	$(LATEX) itp16.tex

itp16.tex: itp16.lagda
	$(AGDA) $(AFLAGS) itp16.lagda

llncs.cls:
	@echo "Downloading LLNCS LaTeX package"
	curl -s ftp://ftp.springer.de/pub/tex/latex/llncs/latex2e/llncs2e.zip \
	     -o llncs2e.zip
	unzip -q llncs2e.zip llncs.cls
	rm llncs2e.zip

clean:
	rm -f itp16.{aux,fls,log,agdai,fdb_latexmk,pdf}

.PHONY: clean
