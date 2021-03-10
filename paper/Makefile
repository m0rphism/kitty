MAIN_TEX=main.tex
SRC_DIR=Paper
TGT_DIR=_build

SRCS=$(wildcard $(SRC_DIR)/*.lagda.tex)
TGTS=$(patsubst $(SRC_DIR)/%.lagda.tex,$(TGT_DIR)/$(SRC_DIR)/%.tex,$(SRCS))
TGTS_INPUT=$(patsubst $(SRC_DIR)/%.lagda.tex,$(SRC_DIR)/%,$(SRCS))

.PHONY: all

all: paper

paper: $(TGTS)
	cp $(MAIN_TEX) $(TGT_DIR)/ ;\
	cd $(TGT_DIR) ;\
	for t in "$(TGTS_INPUT)"; do \
	  sed -i "s|.*SED MARKER.*|  \\\\input{$$t}\\nSED MARKER|g" main.tex; \
	done ;\
	sed -i "/.*SED MARKER.*/d" main.tex ;\
	pdflatex main.tex ;\
	cp main.pdf ../paper.pdf

$(TGT_DIR)/$(SRC_DIR)/%.tex: $(SRC_DIR)/%.lagda.tex
	agda --latex --only-scope-checking --latex-dir=$(TGT_DIR) $^

