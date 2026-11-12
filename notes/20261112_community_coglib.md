# How a community builds CogLib

*2026-11-12. A discussion note, not a plan. Prompted by John Laird's ACT-R 7 conversion
(`notes/20261112_letters_to_Laird.md`) and the question of what CogLib should be if the goal is
not one lab's library but the whole community coming together around CogLean, with CogLib as its
core. Two earlier pieces lead here: `20261030_CMC_CogLean_proposal.md` (the CMC above CogLean)
and `20261110_SHH88_graph_dynamics.md` (how a newcomer brings a paper in).*

## The model: Mathlib, with the parts that won't transfer named

Cognitive science has never built a shared formal artifact; mathematics has built exactly one.
What made Mathlib a community rather than a project:

- one repository with one convention set, so any contribution composes with everything;
- reviewers who enforce the conventions, not the content;
- contributions as small as one lemma;
- impersonal trust: the kernel checks proofs, CI checks the build, a linter checks style, so a
  maintainer never takes a stranger's word;
- generated documentation as the public face;
- a place to talk (Zulip) where a newcomer's first question is answered in an hour;
- a scope everyone already agreed on: standard mathematics is true, so the library records what
  is known.

The last does not transfer. Cognitive science has competing theories, each with a community that
will not accept the other's definitions. A library that fixed "the" definition of memory would be
dead on arrival.

## The design requirement with no Mathlib analogue: host disagreement as content

- **Laws as predicates, not axioms.** Nobody has to agree that memory is determinate. An ACT-R
  contributor and a Soar contributor each add a row; the matrix records the verdicts (has / never
  / lacks), read from theorems; the disagreement becomes a cell rather than an argument.
- **Competing formalizations coexist** as instances at declared fidelity (idealized, realistic,
  replica), with refinement theorems saying how they relate.
- **Evidence judgments** are signed, sourced, contestable records attached to phenomena through
  explicit bridges, never facts the library asserts.
- The library's claim is never "this is how memory works" but "this is what each theory entails,
  checked." Only that claim can be shared across the field; it is the one Newell asked for.

## The barrier is Lean; the way around it is the one already in use

Nearly every line of Lean in CogLean and in John's conversion was written by an agent under a
scientist's supervision. That is the community model, not a footnote about method:

- A cognitive scientist contributes by giving an agent a paper and the library's conventions,
  supervising the postulate table (page citations; `SIMPLIFIED` / `NOT MODELED` / `OPEN` marked)
  and checking fidelity, which is their expertise.
- The library makes agent output **trustworthy without trusting the agent**: the kernel checks
  validity; the axiom check and layering audit check hygiene; the generators check that names
  match statements; differential testing against running software checks replica fidelity; the
  explanatory audit asks what a theorem explains, not only whether it checks.
- **Lean-free contributions are first-class and credited**: a phenomenon stated in careful prose
  for someone to formalize; an evidence judgment with sources and a bridge; a task with its data;
  a critique of a postulate table. Most of the field can make these tomorrow.

## Credit

Mathematicians get credit in papers and treat Mathlib as infrastructure; cognitive scientists will
not spend time on a library that does not count.

- Releases with DOIs; a visible contributors record per theory package and per phenomenon.
- A publication channel for the small results the library produces: a theorem paper is two pages
  ("the 1984 chapter's peaking claim needs a condition"; "Collins and Quillian never shows
  typicality"). A section of an existing journal, or a new venue, turns contributions into
  publications.
- **Author endorsement as a recorded field**: "this formalization of ACT-R's declarative module is
  accepted by its authors as faithful in regime R" is worth more than any proof, and is what
  makes a theory's own community willing to be a row.

## Who convenes it

- Not one lab, and not a new society. The **Common Model of Cognition group** already exists as
  the one place where ACT-R, Soar and Sigma people agree to agree, and John has built its Lean
  version with an ACT-R and a Soar instance. The pitch to that group is one sentence: *the CMC
  made checkable, with every architecture's conformance a theorem.* That brings the architecture
  communities; John and Christian Lebiere are the natural co-conveners and the ACT-R/Soar bridge.
- **Mathematical psychologists** come through laws: they already state them and will recognize
  the matrix as their kind of object.
- **Experimentalists** come through phenomena: they own the evidence layer and the discriminating
  predictions. The Intro paper and CogLean-Intro are the invitation to them.

## Shape of the repository

- A **monorepo core**, as Mathlib is: specifications, laws, phenomena, the matrix and catalog
  generators, the conventions. The smallest core that can host disagreement, and no theory inside
  it, including the founders'.
- **Theories in their owners' repositories**, registered with the core and checked by its CI, as
  Lean's package registry works: a lab keeps its ACT-R package; the core builds it, reads its
  verdicts into the matrix, and refuses it on `sorry`, non-standard axioms or layering
  violations. Competing labs participate without ceding ownership.

## Risks, named

- **Balkanization**: ten ACT-R formalizations with no refinements between them, so the matrix has
  ten rows that should be one. Fix: the fidelity-and-endorsement norm, and the replica tier as a
  shared reference.
- **Rejection by theory owners** ("that's not ACT-R"). Fix: start every theory package from the
  owners or with their review; this is why John and Christian matter more than any technical
  choice.
- **A hundred phenomena nobody uses.** Fix: a phenomenon enters with at least one mechanism held
  to it.
- **Valid but empty agent proofs** (a theorem that restates its premises). Fix: the review norm
  asks what the theorem explains; the explanatory audit is the instrument.

## A sequence

1. The Intro paper and CogLean-Intro (done): the invitation to the phenomena side.
2. John's conversion and the 2026-11-13 conversation: whether the CMC-as-convener idea lands.
3. A short governance and conventions document, modeled on Mathlib's, with the
   disagreement-hosting rules spelled out.
4. A first external theory package built by someone else, with an agent, under the conventions,
   to prove the process works.
5. A CMC-group session.
6. A release with a DOI, the matrices on a public page, and the venue for two-page theorem papers.

## Open

- Whether to raise the convening question with John directly.
- Whether the community goal changes what CogLib's core contains now. The argument here: it
  argues for the smallest core that can host disagreement (specifications, laws, phenomena,
  generators) and against any one theory, including CogLean's own, living inside it.
