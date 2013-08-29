DOC=proof_and_test
SLIDES=hilt_2013_presentation.tex
ABS=proof_and_test_extended_abstract

all: clean doc abstract slides

clean:
	rm -f *.bbl *.aux *.log *.dvi *.blg *.pdf
doc:
	pdflatex "\def\abstractonly{}\input{$(DOC)}"
	bibtex $(DOC)
	pdflatex "\def\abstractonly{}\input{$(DOC)}"
	pdflatex "\def\abstractonly{}\input{$(DOC)}"

abstract:
	cp $(DOC).bib $(ABS).bib
	pdflatex "\def\abstractonly{}\input{$(ABS)}"
	bibtex $(ABS)
	pdflatex "\def\abstractonly{}\input{$(ABS)}"
	pdflatex "\def\abstractonly{}\input{$(ABS)}"
	rm $(ABS).bib

slides:
	pdflatex ${SLIDES}

bib:
	bibtex $(DOC)
