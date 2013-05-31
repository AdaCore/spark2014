DOC=erts_2014

all: doc

clean:
	rm -f *.bbl *.aux *.log *.dvi *.blg *.pdf
doc:
	pdflatex $(DOC)

bib:
	bibtex $(DOC)
