.SUFFIXES: .tex .pdf .long.pdf
LATEX=main

GOALS=${LATEX}.long.pdf \
      ${LATEX}.pdf # should remain the last one to be generated
ALL: $(GOALS)

.tex.pdf:
	pdflatex $^
	bibtex $*
	pdflatex $^
	$(MAKE) clean_tmp

.tex.long.pdf:
	pdflatex "\def\longversion{}\input{$*}"
	pdflatex "\def\longversion{}\input{$*}"
	mv $*.pdf $*.long.pdf
	$(MAKE) clean_tmp

.PHONY: force clean clean_tmp

clean_tmp: force
	rm -f ${LATEX}.aux ${LATEX}.log ${LATEX}.dvi ${LATEX}.toc
	rm -f ${LATEX}.out ${LATEX}.sum texput.log
	rm -f *~

clean: clean_tmp force
	rm -f $(GOALS)

force:
