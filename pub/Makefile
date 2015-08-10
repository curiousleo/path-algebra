itp16.pdf: itp16.tex llncs.cls
	latexmk -pdf itp16.tex # use TEXINPUTS if llncs.cls is in another directory

llncs.cls:
	@echo "Downloading LLNCS LaTeX package"
	curl -s ftp://ftp.springer.de/pub/tex/latex/llncs/latex2e/llncs2e.zip \
	     -o llncs2e.zip
	unzip -q llncs2e.zip llncs.cls
	rm llncs2e.zip
