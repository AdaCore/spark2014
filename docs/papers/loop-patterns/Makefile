.SUFFIXES: .tex .pdf
LATEX=loop_patterns

GOALS=${LATEX}.pdf
ALL: $(GOALS)

.tex.pdf:
	pdflatex $^
	bibtex $*
	pdflatex $^
	$(MAKE) clean_tmp

.PHONY: force clean clean_tmp

clean_tmp: force
	rm -f ${LATEX}.aux ${LATEX}.log ${LATEX}.dvi ${LATEX}.toc
	rm -f ${LATEX}.out ${LATEX}.sum texput.log
	rm -f *~

clean: clean_tmp force
	rm -f $(GOALS)

force:
