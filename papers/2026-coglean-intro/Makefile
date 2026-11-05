all: paper.pdf talk.pdf talk-notes.pdf

paper.pdf: paper.tex refs.bib
	pdflatex -interaction=nonstopmode paper.tex > /dev/null
	bibtex paper > /dev/null
	pdflatex -interaction=nonstopmode paper.tex > /dev/null
	pdflatex -interaction=nonstopmode paper.tex > /dev/null

talk.pdf: talk.tex ../../presentations/preamble.tex
	pdflatex -interaction=nonstopmode talk.tex > /dev/null
	pdflatex -interaction=nonstopmode talk.tex > /dev/null

talk-notes.pdf: talk.tex ../../presentations/preamble.tex
	pdflatex -interaction=nonstopmode -jobname=talk-notes "\\def\\withnotes{}\\input{talk.tex}" > /dev/null
	pdflatex -interaction=nonstopmode -jobname=talk-notes "\\def\\withnotes{}\\input{talk.tex}" > /dev/null

clean:
	rm -f *.aux *.log *.out *.bbl *.blg *.toc *.nav *.snm *.vrb

.PHONY: all clean
