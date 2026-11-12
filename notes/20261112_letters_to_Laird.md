# Two letters to John Laird (2026-11-12)

Context. John sent `Laird-ACT-CMC/`: `actr-lean.tar.gz` (a Lean 4 replica of ACT-R 7.27.7, about
7,600 lines, validated trace for trace against ACT-R under SBCL: ~8,600 model runs and 72 tasks
identical) and `ACT-R-on-CMC-Analysis-v6.docx` (alignment with the CMC relative to Soar). The
review's conclusions: it is an executable specification validated by testing, with about 30
structural theorems and `Float32` arithmetic; the tarball lacks the `CMC/` and `Soar/` modules its
lakefile and `Conform.lean` need; its `retrieve` is argmax-of-activation plus threshold, which
confirms the Intro paper's ACT-R footnote and suggests the real ACT-R's matrix row differs from
CogLean's softmax formalization (determinate and certain without noise). The first letter asks for
what is missing to build and run it; the second proposes the joint library.

---

## Letter 1: what is needed to build and run the tarball

John,

Thanks for the ACT-R conversion and the analysis; this is impressive work, and the
differential-testing method is exactly right. I'd like to build and run it here, and the tarball
isn't quite self-contained. Could you send the missing pieces?

**To build.** The `lakefile.lean` declares three libraries, `CMC`, `Soar` and `ACTR`, and two
executables, `soar-lean` (root `Main`) and `actr-lean`, but the tarball contains only `ACTR/`,
`ACTR.lean`, `ActrMain.lean`, the lakefile and `tools/actr/`. So I'm missing:

- the `CMC/` directory (`ACTR/Conform.lean` imports `CMC.Meta`; the `CMC.lean` and
  `CMC_Meta.lean` you sent on October 30 are flat files for Lean 4.15, so I assume the module
  layout has changed since);
- the `Soar/` directory and `Main.lean`, if you want me to be able to build the whole `cmcsoar`
  package rather than just the ACT-R library;
- `lean-toolchain` and `lake-manifest.json`, so I'm on the same Lean version and dependencies
  (your README says 4.35.0 and core only; I just want to be sure nothing else is required).

Simplest would be a tarball of the whole `cmcsoar` directory minus `.lake/`.

**To run the comparisons.** `tools/actr/task.lisp` and the diff scripts assume ACT-R 7.27.7
running under SBCL 2.2.9 with the tutorial. I have the ACT-R 7 standalone here but not the source
tree. Two questions:

- What exactly is your ACT-R side: the asmaloney GitHub mirror at a particular commit, loaded in
  SBCL from source? If you can tell me the commit and how you load it (and the tutorial directory
  it expects), I'll reproduce it.
- Could you also include the recorded task logs (the `.log` files `task.lisp` produces) and the
  ACT-R traces for the regression? With those I can replay everything with `actr-lean --script`
  and rerun the diffs without first standing up the Lisp side, which would let me check the
  "72 of 72 identical" result immediately.

Nothing else is needed; the ACT-R library itself looks complete, and I'll report anything I find.

Jeff

---

## Letter 2: the joint vision

John,

Beyond getting the package to build, I want to put a larger idea to you, because the ACT-R
conversion changed how I see what we're each doing.

On October 30 I sent you a note proposing that the CMC sits *above* CogLean: your `Arch`
structure defines what a conforming architecture is, and CogLean's mechanisms could be candidate
fillers for its slots, each fit a theorem. I still think that's right, but it was half the
picture. Your ACT-R replica supplies the other half: CogLean's mechanisms also need something
*below* them, a reference implementation they can be proved faithful to in a stated regime. Our
ACT-R memory is exact and provable and small (decay 1, no noise, one softmax), and every paper we
write carries a footnote about how simplified it is. Your ACT-R is the real thing, trace for
trace, and, as your analysis says, almost nothing about its behavior can be proved, because it's
floats and tables. Neither of us can do what the other does. Together the two are a library.

What struck me most is that we've been running the same method at different grains. Your Table 2
is a theory matrix: rows are architectures, columns are the CMC's commitments, and each cell is
kept or departs, read from a theorem where one exists. Our memory matrix has the same form with
memories for rows and behavioral laws (a studied item retrieves itself; studying one item doesn't
disturb another) for columns. The CMC's obligations are laws over architectures; ours are laws
over mechanisms. Your Section 4, the commitments ACT-R and Soar share that the CMC doesn't state,
is the matrix finding new columns.

So here is the library I think we should be building, in Mathlib's terms. A hierarchy of
*specifications* of cognitive components, from a memory or a selector up to a whole architecture,
with the CMC as the top of that hierarchy rather than an external standard. *Laws* as predicates
over instances (not axioms, because theories differ by which laws they satisfy, and the matrices
need "never" to be expressible). *Instances at declared fidelity*: idealized and provable,
realistic over the reals, and replica, trace-validated against the running software, with your
`SIMPLIFIED` / `NOT MODELED` / `OPEN` markers as the library-wide discipline. And *refinement
theorems* connecting the tiers: this idealized memory computes what that realistic one does at
decay 1; your `retrieve` is argmax-plus-threshold of your activation function. Once those exist,
a phenomenon proved on the provable tier is a theorem about ACT-R in a stated regime, not about a
"formalized family," and the departures your Conform file records become properties of instances
rather than obstacles to them. Above all that, tasks with their data (your tutorial tasks already
carry ACT-R's data for the fan effect, paired associates, Zbrodoff and Siegler), phenomena stated
against the specifications, and the evidence about people attached through explicit bridges.

I'd like to start small and concrete. One vertical slice, memory, where we both already have
everything: the specification with its six laws; three instances (our exact memory, a realistic
one over the reals with ACT-R's actual retrieval shape, and your declarative module imported
untouched); the two refinements; the matrix row for the real ACT-R, which I expect to differ from
ours (without noise your retrieve is determinate and certain above threshold; ours never is,
because of the softmax); and one phenomenon, probably the fan effect from spreading activation,
proved once and inherited by your replica. Your files wouldn't change; everything would live in a
bridge that imports both. If the slice works, the rest migrates a component at a time, and the
CMC instance for ACT-R falls out of it once the retrieval-result question is settled with
Christian.

Two questions for you. First, does this match your sense of where the CMC work should go, and
would you want the architecture specification to be a shared top of one hierarchy, or kept as
your artifact that the rest imports? Either works; the first reaches further. Second, the
realistic tier needs real numbers, which means Mathlib in the core rather than confined to a side
package as I've had it; do you have a view, given that your replicas are core-only by design?

I'm not proposing you change anything you've built. I'm proposing that what you've built is the
bottom and the top of the thing I've been trying to build the middle of.

Jeff
