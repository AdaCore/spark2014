.SUFFIXES: .tex .pdf
LATEX=gnat

ALL: ${LATEX}.pdf

.tex.pdf:
	pdflatex $^
	pdflatex $^ # repeated for table of contents

${LATEX}.pdf: ${LATEX}.title.pdf ${LATEX}.main.pdf
	pdfsam-console -overwrite -f $(PWD)/${LATEX}.title.pdf \
	 -f $(PWD)/${LATEX}.main.pdf -o $(PWD)/${LATEX}.pdf concat

install: ${LATEX}.pdf
	cp -f $^ ../../slides

.PHONY: clean_tmp clean

clean_tmp: force
	rm -f *.aux *.log *.dvi *.toc *.nav *.vrb *.snm
	rm -f *.out *.sum texput.log
	rm -f _whizzy_* *~

clean: clean_tmp force
	rm -f *.pdf *.ps

force:
