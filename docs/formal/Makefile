# Build the Stanley-style formal companion PDF.
#
# Requires a LaTeX distribution with pdflatex (or lualatex), the
# `listings`, `hyperref`, `amsthm`, `cleveref`, `xcolor`, `geometry`
# packages, and the `lmodern` font package.
#
# On Debian/Ubuntu / GitHub Actions runners:
#   sudo apt-get install -y \
#     texlive-latex-base texlive-latex-recommended texlive-latex-extra \
#     texlive-fonts-recommended texlive-fonts-extra texlive-science
#
# Usage:
#   make            # build PDF with pdflatex (default)
#   make lua        # build PDF with lualatex
#   make clean      # remove auxiliary files
#   make distclean  # remove PDF too

MAIN     := eulerian_formal
ENGINE   := pdflatex
LUAENGINE := lualatex
FLAGS    := -interaction=nonstopmode -file-line-error

.PHONY: all pdf lua clean distclean

all: pdf

pdf: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex preamble.tex
	$(ENGINE) $(FLAGS) $(MAIN).tex
	$(ENGINE) $(FLAGS) $(MAIN).tex   # second pass for refs/TOC

lua:
	$(LUAENGINE) $(FLAGS) $(MAIN).tex
	$(LUAENGINE) $(FLAGS) $(MAIN).tex

clean:
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).toc $(MAIN).out \
	      $(MAIN).fls $(MAIN).fdb_latexmk $(MAIN).synctex.gz \
	      $(MAIN).bbl $(MAIN).blg $(MAIN).idx $(MAIN).ind \
	      $(MAIN).ilg $(MAIN).lof $(MAIN).lot $(MAIN).nav \
	      $(MAIN).snm

distclean: clean
	rm -f $(MAIN).pdf
