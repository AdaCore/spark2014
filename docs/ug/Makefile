# Makefile for Sphinx documentation
#

# Main mode for generating SPARK User's Guide:
#  - full for the complete documentation
#  - core for a core subset of the documentation, suitable for translation in
#    other languages. In that case, you also need to update files index.rst,
#    gnatprove.rst and spark_2014.rst to uncomment the lines that conditionally
#    change the toctree for core mode. Indeed, Sphinx does not support
#    currently conditional changes to the toctree, so leaving these lines
#    uncommented leads to broken toctree.
#  - core_ja for the Japanese version of the core subset of the documentation.
#    To build the Japanese HTML version, type
#      MODE=core_ja make html
#    To build the Japanese PDF version, follow the following instructions:
#      - install all texlive packages that are needed to compile the english
#        version of the PDF, like texlive-fonts-recommended and
#        texlive-latex-extra
#      - install the texlive-lang-japanese package
#      - $ MODE=core_ja make latex
#      - $ cd _build/latex
#      - edit spark2014_ug.tex and add the following line before package
#        sphinx is included:
#        \usepackage[dvipdfmx]{graphicx}
#      - $ make all-pdf-ja
MODE ?= full

# You can set these variables from the command line.
SPHINXOPTS    = -W -t $(MODE)
SPHINXBUILD   = sphinx-build
PAPER         =
BUILDDIR      = _build
VERSION       = 0.0w

# Internal variables.
PAPEROPT_a4     = -D latex_paper_size=a4
PAPEROPT_letter = -D latex_paper_size=letter
ALLSPHINXOPTS   = -d $(BUILDDIR)/doctrees $(PAPEROPT_$(PAPER)) $(SPHINXOPTS) .

GENERATED_RST_FILES = en/source/flow_checks_table.rst en/source/proof_checks_table.rst

.PHONY: help clean html dirhtml singlehtml pickle json htmlhelp qthelp devhelp epub latex latexpdf text man changes linkcheck doctest setup

help:
	@echo "Please use \`make <target>' where <target> is one of"
	@echo "  html       to make standalone HTML files"
	@echo "  dirhtml    to make HTML files named index.html in directories"
	@echo "  singlehtml to make a single large HTML file"
	@echo "  pickle     to make pickle files"
	@echo "  json       to make JSON files"
	@echo "  htmlhelp   to make HTML files and a HTML help project"
	@echo "  qthelp     to make HTML files and a qthelp project"
	@echo "  devhelp    to make HTML files and a Devhelp project"
	@echo "  epub       to make an epub"
	@echo "  latex      to make LaTeX files, you can set PAPER=a4 or PAPER=letter"
	@echo "  latexpdf   to make LaTeX files and run them through pdflatex"
	@echo "  text       to make text files"
	@echo "  man        to make manual pages"
	@echo "  changes    to make an overview of all changed/added/deprecated items"
	@echo "  linkcheck  to check all external links for integrity"
	@echo "  doctest    to run all doctests embedded in the documentation (if enabled)"

$(GENERATED_RST_FILES): table_generator/table_generator.adb
	gprbuild -p -P table_generator/table_generator
	table_generator/obj/table_generator

setup:	$(GENERATED_RST_FILES)
	echo "version = '$(VERSION)'" > ../sphinx_support/confvars.py

clean:
	(cd gnatprove_by_example; make -f Makefile.examples clean)
	-rm -rf $(BUILDDIR)/*
	gprclean -P table_generator/table_generator
	rm -f $(GENERATED_RST_FILES)

generate:
	@echo "Generating GNATprove results..."
	#(cd gnatprove_by_example; make -f Makefile.examples gnatprove results)
	(cd examples; ./run_examples.py)

generate-nightly:
	@echo "Generating GNATprove results..."
	#(cd gnatprove_by_example; make -f Makefile.examples clean gnatprove results clean)
	(cd examples; ./run_examples.py)

html: setup
	$(SPHINXBUILD) -b html $(ALLSPHINXOPTS) $(BUILDDIR)/html
	@echo
	@echo "Build finished. The HTML pages are in $(BUILDDIR)/html."

dirhtml: setup
	$(SPHINXBUILD) -b dirhtml $(ALLSPHINXOPTS) $(BUILDDIR)/dirhtml
	@echo
	@echo "Build finished. The HTML pages are in $(BUILDDIR)/dirhtml."

singlehtml: setup
	$(SPHINXBUILD) -b singlehtml $(ALLSPHINXOPTS) $(BUILDDIR)/singlehtml
	@echo
	@echo "Build finished. The HTML page is in $(BUILDDIR)/singlehtml."

pickle: setup
	$(SPHINXBUILD) -b pickle $(ALLSPHINXOPTS) $(BUILDDIR)/pickle
	@echo
	@echo "Build finished; now you can process the pickle files."

json: setup
	$(SPHINXBUILD) -b json $(ALLSPHINXOPTS) $(BUILDDIR)/json
	@echo
	@echo "Build finished; now you can process the JSON files."

htmlhelp: setup
	$(SPHINXBUILD) -b htmlhelp $(ALLSPHINXOPTS) $(BUILDDIR)/htmlhelp
	@echo
	@echo "Build finished; now you can run HTML Help Workshop with the" \
	      ".hhp project file in $(BUILDDIR)/htmlhelp."

qthelp: setup
	$(SPHINXBUILD) -b qthelp $(ALLSPHINXOPTS) $(BUILDDIR)/qthelp
	@echo
	@echo "Build finished; now you can run "qcollectiongenerator" with the" \
	      ".qhcp project file in $(BUILDDIR)/qthelp, like this:"
	@echo "# qcollectiongenerator $(BUILDDIR)/qthelp/GNATproveUsersGuide.qhcp"
	@echo "To view the help file:"
	@echo "# assistant -collectionFile $(BUILDDIR)/qthelp/GNATproveUsersGuide.qhc"

devhelp: setup
	$(SPHINXBUILD) -b devhelp $(ALLSPHINXOPTS) $(BUILDDIR)/devhelp
	@echo
	@echo "Build finished."
	@echo "To view the help file:"
	@echo "# mkdir -p $$HOME/.local/share/devhelp/GNATproveUsersGuide"
	@echo "# ln -s $(BUILDDIR)/devhelp $$HOME/.local/share/devhelp/GNATproveUsersGuide"
	@echo "# devhelp"

epub: setup
	$(SPHINXBUILD) -b epub $(ALLSPHINXOPTS) $(BUILDDIR)/epub
	@echo
	@echo "Build finished. The epub file is in $(BUILDDIR)/epub."

latex: setup
	$(SPHINXBUILD) -b latex $(ALLSPHINXOPTS) $(BUILDDIR)/latex
	@echo
	@echo "Build finished; the LaTeX files are in $(BUILDDIR)/latex."
	@echo "Run \`make' in that directory to run these through (pdf)latex" \
	      "(use \`make latexpdf' here to do that automatically)."

latexpdf: setup
	$(SPHINXBUILD) -b latex $(ALLSPHINXOPTS) $(BUILDDIR)/latex
	@echo "Running LaTeX files through pdflatex..."
	make -C $(BUILDDIR)/latex all-pdf
	@echo "pdflatex finished; the PDF files are in $(BUILDDIR)/latex."

text: setup
	$(SPHINXBUILD) -b text $(ALLSPHINXOPTS) $(BUILDDIR)/text
	@echo
	@echo "Build finished. The text files are in $(BUILDDIR)/text."

man: setup
	$(SPHINXBUILD) -b man $(ALLSPHINXOPTS) $(BUILDDIR)/man
	@echo
	@echo "Build finished. The manual pages are in $(BUILDDIR)/man."

changes: setup
	$(SPHINXBUILD) -b changes $(ALLSPHINXOPTS) $(BUILDDIR)/changes
	@echo
	@echo "The overview file is in $(BUILDDIR)/changes."

linkcheck: setup
	$(SPHINXBUILD) -b linkcheck $(ALLSPHINXOPTS) $(BUILDDIR)/linkcheck
	@echo
	@echo "Link check complete; look for any errors in the above output " \
	      "or in $(BUILDDIR)/linkcheck/output.txt."

doctest: setup
	$(SPHINXBUILD) -b doctest $(ALLSPHINXOPTS) $(BUILDDIR)/doctest
	@echo "Testing of doctests in the sources finished, look at the " \
	      "results in $(BUILDDIR)/doctest/output.txt."
