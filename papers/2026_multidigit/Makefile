paper.pdf: paper.tex refs.bib
	pdflatex -interaction=nonstopmode paper.tex > /dev/null
	bibtex paper > /dev/null
	pdflatex -interaction=nonstopmode paper.tex > /dev/null
	pdflatex -interaction=nonstopmode paper.tex > /dev/null

clean:
	rm -f *.aux *.log *.out *.bbl *.blg *.toc

.PHONY: clean
