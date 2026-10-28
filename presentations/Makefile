DECKS = coglean-overview recognition-retrieval recognition-retrieval-lean laws-matrix-experiments blind-simulation

all: $(DECKS:=.pdf) $(DECKS:=-notes.pdf)

%.pdf: %.tex preamble.tex
	pdflatex -interaction=nonstopmode $< > /dev/null
	pdflatex -interaction=nonstopmode $< > /dev/null

%-notes.pdf: %.tex preamble.tex
	pdflatex -interaction=nonstopmode -jobname=$*-notes "\def\withnotes{}\input{$*.tex}" > /dev/null
	pdflatex -interaction=nonstopmode -jobname=$*-notes "\def\withnotes{}\input{$*.tex}" > /dev/null

clean:
	rm -f *.aux *.log *.nav *.out *.snm *.toc *.vrb

.PHONY: all clean
