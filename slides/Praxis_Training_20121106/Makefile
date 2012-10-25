ALL: gnat.pdf gnat2why.pdf gnatprove.pdf

%.pdf: %.tex
	pdflatex $^
	pdflatex $^ # repeated for table of contents

%.pdf: %.title.pdf %.main.pdf
	pdfsam-console -overwrite -f $(PWD)/$*.title.pdf \
	 -f $(PWD)/$*.main.pdf -o $(PWD)/$*.pdf concat

.PHONY: clean_tmp clean

clean_tmp: force
	rm -f *.aux *.log *.dvi *.toc *.nav *.vrb *.snm
	rm -f *.out *.sum texput.log
	rm -f _whizzy_* *~

clean: clean_tmp force
	rm -f *.pdf *.ps

force:
