paper.pdf: paper.tex refs.bib spec.tex
	latexmk -pdf -interaction=nonstopmode paper.tex

spec.tex: ../sim/SPEC.md gen_spec.sh
	./gen_spec.sh

clean:
	latexmk -C
