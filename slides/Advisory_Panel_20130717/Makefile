SHELL=/bin/bash

BASE=.
TEXINPUTS=$(BASE)/altran_latex_style
TEXFONTS=$(BASE)/altran_latex_style

all: AP_telcon_slides_20130717.pdf

%.pdf: %.tex
	export TEXINPUTS=$(TEXINPUTS):.:; \
	export TEXFONTS=$(TEXFONTS): ; \
	pdflatex $< ; \
	pdflatex $<

clean:
	rm -rf AP_telcon_slides_20130717.pdf *.aux *.out *.log *.snm *.toc *.vrb *.nav
