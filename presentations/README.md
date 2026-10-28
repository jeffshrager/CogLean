# Presentations

Four Beamer decks about CogLean. Each comes as slides alone (`deck.pdf`) and as slides with speaker notes (`deck-notes.pdf`, a notes page after each slide).

| Deck | Audience | Slides |
|---|---|---|
| `coglean-overview` | a general cognitive science audience: the idea, laws and families, the theory matrix, what is true here, two examples, limits | 15 |
| `recognition-retrieval` | detailed: the multi-digit model (EPAM + DOA), confident errors, the blind simulation, swapping in ACT-R, the extracted composition, face naming, confident errors from laws | 12 |
| `recognition-retrieval-lean` | partner to the deck above, for readers who want the proofs: the actual Lean code, layer by layer (exact distributions, the two-stage lemma, discrimination nets and Lemma A, DOA search and its closed form, the composition, `confident_errors` and a supporting lemma, memory as an interface, the bridge to multi-digit addition, laws, `studied_selfRetrieval`, `confident_errors_of_laws`, an instance, computing with `decide +kernel`, what is trusted). Each code slide is preceded by an "In words" slide stating its definitions and theorems in English, with proof sketches; read in order, they give the whole proof in words | 34 |
| `laws-matrix-experiments` | detailed: the six laws, four families, the matrix and evidence row, the prototype study-test, the AB/BA experiment derived from laws, forced choice | 15 |

```sh
cd presentations && make        # builds all six PDFs (pdflatex, two passes each)
make clean                      # removes LaTeX auxiliary files
```

`preamble.tex` holds the shared styling and the notes switch; `leancode.tex` sets up Lean source listings (Unicode mapped for pdflatex). Code on the slides is quoted from the repository, lightly trimmed, with `-- ...` marking omissions. The numbers on the slides are the library's theorems and exact computations, as of commit `fb60b6e`. If a result changes, update the slide.
