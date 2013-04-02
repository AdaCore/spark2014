export TEXINPUTS:=.:./springer_sttt_macro_pack/:
DOC=sttt_2013

all: doc

clean:
	rm -f *.bbl *.aux *.log *.dvi *.blg *.pdf
doc:
	pdflatex $(DOC)
	bibtex $(DOC)
	pdflatex $(DOC)
	pdflatex $(DOC)

bib:
	bibtex $(DOC)
