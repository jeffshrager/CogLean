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

## Letter 2: a thought for tomorrow

John,

One thing to put on the table for tomorrow, tentatively.

Reading the ACT-R conversion alongside what we've been doing, I keep seeing the same method at two
grains. Your Table 2 is a theory matrix: architectures against the CMC's commitments, each cell a
theorem. Ours is memories against behavioral laws. And the two efforts are complementary in a way
I hadn't appreciated: your replicas are exactly faithful and hard to prove things about; ours are
provable and admittedly simplified. The thing that would connect them is a refinement theorem, of
the form "our idealized memory computes what your declarative module does, at decay 1 and without
noise."

That suggests a picture where the CMC is the top of one hierarchy of specifications and your
replicas are its bottom, with provable mechanisms in the middle and phenomena stated above. I'm not
sure it's right, and I don't want to design it on paper. If it interests you, a small first test
would be memory alone: one specification, our instance and yours, the refinement between them, and
the real ACT-R's row of the matrix, which I suspect differs from ours.

Something to talk about, nothing more yet.

Jeff
