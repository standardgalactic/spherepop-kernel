#!/bin/sh
# Concatenate the parts into one self-contained .tex (bibliography inside) and compile.
set -e
cd "$(dirname "$0")/.."
python3 tools/transcripts.py >/dev/null
python3 tools/excerpts.py >/dev/null
cat book/00_preamble.tex book/01_preface.tex book/02_part1.tex book/03_regs.tex book/04_part2.tex book/05_part3.tex book/06_back.tex > spherepop_languages.tex
pdflatex -interaction=nonstopmode -halt-on-error spherepop_languages.tex >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error spherepop_languages.tex >/dev/null
