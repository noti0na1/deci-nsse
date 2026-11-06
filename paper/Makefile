# Build the paper with latexmk (pdflatex + bibtex).
#
#   make          build main.pdf
#   make watch    rebuild continuously while editing
#   make clean    remove auxiliary files, keep the PDF
#   make distclean remove auxiliary files and the PDF

MAIN    := main
LATEXMK := latexmk
FLAGS   := -pdf -interaction=nonstopmode -halt-on-error -file-line-error

SOURCES := $(MAIN).tex macros.tex refs.bib $(wildcard sections/*.tex) $(wildcard figures/*.tex)

.PHONY: all watch clean distclean

all: $(MAIN).pdf

$(MAIN).pdf: $(SOURCES)
	$(LATEXMK) $(FLAGS) $(MAIN).tex

watch:
	$(LATEXMK) $(FLAGS) -pvc $(MAIN).tex

clean:
	$(LATEXMK) -c $(MAIN).tex
	rm -f $(MAIN).bbl $(MAIN).run.xml comment.cut

distclean: clean
	$(LATEXMK) -C $(MAIN).tex
