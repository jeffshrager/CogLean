# Presentations

Three Beamer decks about CogLean. Each comes as slides alone (`deck.pdf`) and as slides with speaker notes (`deck-notes.pdf`, a notes page after each slide).

| Deck | Audience | Slides |
|---|---|---|
| `coglean-overview` | a general cognitive science audience: the idea, laws and families, the theory matrix, what is true here, two examples, limits | 15 |
| `recognition-retrieval` | detailed: the multi-digit model (EPAM + DOA), confident errors, the blind simulation, swapping in ACT-R, the extracted composition, face naming, confident errors from laws | 12 |
| `laws-matrix-experiments` | detailed: the six laws, four families, the matrix and evidence row, the prototype study-test, the AB/BA experiment derived from laws, forced choice | 15 |

```sh
cd presentations && make        # builds all six PDFs (pdflatex, two passes each)
make clean                      # removes LaTeX auxiliary files
```

`preamble.tex` holds the shared styling and the notes switch. The numbers on the slides are the library's theorems and exact computations, as of commit `fb60b6e`. If a result changes, update the slide.
