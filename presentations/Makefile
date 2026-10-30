DECKS = catalog doa-simulation coglean-overview conceptual-combination knowledge-concepts problem-solving multidigit-model recognition-retrieval recognition-retrieval-lean laws-matrix-experiments blind-simulation coglean-story

all: $(DECKS:=.pdf) $(DECKS:=-notes.pdf)

%.pdf: %.tex preamble.tex
	pdflatex -interaction=nonstopmode $< > /dev/null
	pdflatex -interaction=nonstopmode $< > /dev/null

%-notes.pdf: %.tex preamble.tex
	pdflatex -interaction=nonstopmode -jobname=$*-notes "\def\withnotes{}\input{$*.tex}" > /dev/null
	pdflatex -interaction=nonstopmode -jobname=$*-notes "\def\withnotes{}\input{$*.tex}" > /dev/null

coglean-story.tex: gen_story.py coglean-overview.tex recognition-retrieval.tex recognition-retrieval-lean.tex blind-simulation.tex laws-matrix-experiments.tex
	python3 gen_story.py

clean:
	rm -f *.aux *.log *.nav *.out *.snm *.toc *.vrb

.PHONY: all clean
