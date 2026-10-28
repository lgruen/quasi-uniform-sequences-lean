# Makefile -- Low-discrepancy quasi-uniform digital sequences in every dimension (version 1)
#   make pdf    compile main.pdf with tectonic (figures from figs/, bibliography refs.bib)
#   make png    render page 1 of main.pdf to main-p1.png (needs pdftoppm or sips)
#   make clean  remove the PDF and aux files
# Without tectonic: latexmk -pdf main.tex (or pdflatex, bibtex, pdflatex, pdflatex). main.bbl is the bibliography as
# built by tectonic; it is used when BibTeX is not run.
TECTONIC := $(shell command -v tectonic 2>/dev/null)
PDFTOPPM := $(shell command -v pdftoppm 2>/dev/null)
DOC      := main
SECTIONS := $(wildcard sections/*.tex)

.PHONY: pdf png clean
pdf: $(DOC).pdf

$(DOC).pdf: $(DOC).tex refs.bib $(SECTIONS)
ifneq ($(TECTONIC),)
	$(TECTONIC) -X compile --keep-logs --keep-intermediates $(DOC).tex
else
	@echo "ERROR: tectonic not found (https://tectonic-typesetting.github.io; or use latexmk -pdf main.tex)"; exit 1
endif

png: $(DOC).pdf
ifneq ($(PDFTOPPM),)
	$(PDFTOPPM) -png -r 110 -f 1 -l 1 -singlefile $(DOC).pdf $(DOC)-p1
else
	sips -s format png $(DOC).pdf --out $(DOC)-p1.png >/dev/null
endif

clean:
	rm -f $(DOC).pdf $(DOC).aux $(DOC).log $(DOC).out $(DOC).blg $(DOC)-p1.png
