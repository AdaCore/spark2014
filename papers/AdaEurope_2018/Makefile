SRCTEX=$(wildcard *.tex)

all: paper.pdf

paper.pdf: $(SRCTEX) references.bib
	latexmk -pdf paper



clean:
	rm -f *.o *.aux *.log *.out *.bbl *.toc *.pdf *.blg *.dvi *~ *.fls *_latexmk *.lof
