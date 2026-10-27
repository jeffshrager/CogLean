#!/bin/sh
# Generate spec.tex (the appendix) from the blind simulation's prose spec.
# Drops the spec's title, numbers its sections A.1-A.10 (matching "section N"
# in its text), makes the few non-ASCII symbols math, and wraps code lines.
sed -e '1d' -e 's/^## [0-9]*\. /## /' -e 's/^### [0-9.]* /### /' ../sim/SPEC.md |
  pandoc -f markdown -t latex --no-highlight --wrap=preserve 2>/dev/null |
  sed -e 's/≤/$\\le$/g' -e 's/≥/$\\ge$/g' \
      -e 's/⌊/$\\lfloor$/g' -e 's/⌋/$\\rfloor$/g' \
      -e 's/\\begin{verbatim}/\\begin{Verbatim}[breaklines,breakanywhere,fontsize=\\footnotesize]/' \
      -e 's/\\end{verbatim}/\\end{Verbatim}/' > spec.tex
