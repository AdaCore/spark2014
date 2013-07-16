SHELL=/bin/bash


all: AP_telcon_slides_20130717.pdf

%.pdf: %.tex
	pdflatex $< ; \
	pdflatex $<

clean:
	rm -rf AP_telcon_slides_20130717.pdf *.aux *.out *.log *.snm *.toc *.vrb *.nav
