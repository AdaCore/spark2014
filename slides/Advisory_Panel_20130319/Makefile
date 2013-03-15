SHELL=/bin/bash

BASE=../..
TEXINPUTS=$(BASE)/altran_latex_style
TEXFONTS=$(BASE)/altran_latex_style

all: AP_telcon_slides_20130319.pdf

%.pdf: %.tex
	export TEXINPUTS=$(TEXINPUTS):.:; \
	export TEXFONTS=$(TEXFONTS): ; \
	pdflatex $< ; \
	pdflatex $<

clean:
	rm -rf *.pdf *.out *.log *.snm *.toc *.vrb *.nav
