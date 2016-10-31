DOC=nfm_2017

all: doc

clean:
	rm -f *.bbl *.aux *.log *.dvi *.blg *.pdf

abstract:
	make clean
	pdflatex "\def\abstractonly{}\input{$(DOC)}"
	bibtex $(DOC)
	pdflatex "\def\abstractonly{}\input{$(DOC)}"
	pdflatex "\def\abstractonly{}\input{$(DOC)}"

doc:
	make clean
	pdflatex $(DOC)
	bibtex $(DOC)
	pdflatex $(DOC)
	pdflatex $(DOC)

bib:
	bibtex $(DOC)
