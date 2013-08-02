DOC=proof_and_test

all: doc

clean:
	rm -f *.bbl *.aux *.log *.dvi *.blg *.pdf
doc:
	make clean
	pdflatex "\def\abstractonly{}\input{$(DOC)}"
	bibtex $(DOC)
	pdflatex "\def\abstractonly{}\input{$(DOC)}"
	pdflatex "\def\abstractonly{}\input{$(DOC)}"

bib:
	bibtex $(DOC)
