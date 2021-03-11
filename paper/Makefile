MAIN_TEX=paper.tex
MAIN_PDF=paper.pdf
LAGDA_DIR=Paper
CACHE_DIR=_build
EXTRA_FILES=$(wildcard *.bib *.cls *.sty *.tex)

SRCS=$(wildcard $(LAGDA_DIR)/*.lagda.tex)
TGTS=$(patsubst $(LAGDA_DIR)/%.lagda.tex,$(CACHE_DIR)/$(LAGDA_DIR)/%.tex,$(SRCS))
TGTS_INPUT=$(patsubst $(LAGDA_DIR)/%.lagda.tex,$(LAGDA_DIR)/%,$(SRCS))

.PHONY: all

all: paper

paper: $(TGTS)
	cp $(MAIN_TEX) $(CACHE_DIR)/main.tex	                               ;\
	cp $(EXTRA_FILES) $(CACHE_DIR)/				                               ;\
	cd $(CACHE_DIR)												                               ;\
	for t in "$(TGTS_INPUT)"; do                                          \
	  sed -i "s|.*SED MARKER.*|  \\\\input{$$t}\\nSED MARKER|g" main.tex ;\
	done																	                               ;\
	sed -i "/.*SED MARKER.*/d" main.tex		                               ;\
	pdflatex main.tex											                               ;\
	bibtex main														                               ;\
	pdflatex main.tex											                               ;\
	pdflatex main.tex

	cp $(CACHE_DIR)/main.pdf $(MAIN_PDF)

$(CACHE_DIR)/$(LAGDA_DIR)/%.tex: $(LAGDA_DIR)/%.lagda.tex
	agda --latex --only-scope-checking --latex-dir=$(CACHE_DIR) $^
