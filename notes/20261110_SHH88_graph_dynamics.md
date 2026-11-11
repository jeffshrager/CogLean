# Bringing Shrager, Hogg & Huberman (1988) into CogLean: an analysis

*Recorded 2026-11-10, for later. Nothing has been built. The question was methodological as much
as scientific: how would someone arriving at CogLean with this paper (or just its idea) make use
of the library, and eventually blend the work into CogLib, given how many parts already
interact?*

Shrager, J., Hogg, T., & Huberman, B. A. (1988). A graph-dynamic model of the power law of
practice and the problem-solving fan-effect. *Science, 242*, 414–416. Text at
`~/Desktop/personal/pubs/pubs_OCRed/1988PowerLaw_OCRed.pdf`.

## 1. What the paper says

- **The bit game.** A state is a B-bit vector (B = 5 in most runs). A trial draws a start and a
  goal state at random and searches by applying operators. An operator is a pattern→result pair
  with don't-care bits (`?1?1? → ?0?0?`), applicable when the fixed bits match; it flips the bits
  that differ. Play begins with the 2B one-bit operators, which form the hypercube, so every
  state is reachable from every other. Performance on a trial is the number of edges traversed.
- **The decision procedure, parameter r.** At a state, find the applicable operators; call
  "good" those that minimize the Hamming distance to the goal after application and "bad" the
  rest; remove each bad one with probability r; choose uniformly from what remains. r = 1 is a
  (heuristic) optimal procedure, r = 0 a random walk, r = 0.5 "mediocre".
- **Learning.** After each trial, in the style of Soar chunking, add the operator that most
  generally summarizes the solution: for the game `01110 → 10101` the new operator is
  `01?10 → 10?01`, with `?` where a bit did not change. It solves that game in one step and adds
  2^k directed edges for k unchanged bits.
- **Simulation results (Fig. 1, 16,384 observations per point, trials 1–100 on log-log).**
  At r = 1 and r = 0, solution rate improves and the curves look straight on log-log, read as
  the power law. At r = 0.5, performance first *degrades* as operators are added: the
  problem-solving fan effect.
- **The theory.** Idealize the problem space as a random graph on n nodes with edge probability
  p, mean degree μ = (n−1)p; assume uniform branching and long cycles (tree-like), so the start
  and goal are about the diameter D = ln n / ln μ apart; at each node one edge leads toward the
  goal and (μ−1)(1−r) effective bad edges away. The search becomes a biased one-dimensional
  walk on {0,…,D} with P₋ = 1/(1 + (μ−1)(1−r)) toward the goal. Eq. 2 is the expected hitting
  time s(P₋, D). Regimes: drift when P₋ > ½ (s ≈ D/(P₋−P₊)); diffusion when P₋ < ½ (s grows
  exponentially in D). Adding links lowers D but raises μ; s falls when the decision procedure
  is strong (r near 1: s ≈ ln n / ln μ) or absent (r = 0), and rises over a range when
  |ln(1−r)| ln n > (ln μ)², the fan effect.
- **The class-level claim (last paragraph).** Against ACT*'s rule strengthening (which puts a
  power law in) and Rosenbloom's chunking (power law only from subgoal chunking): "we predict a
  power law for any sort of operator addition (in the appropriate decision-procedure regimes)".

## 2. The paper in CogLean's categories

The paper does not separate these; CogLean does, and the separation is the first thing a
newcomer should do, on paper, before any Lean (as `StrategyChoice/Postulates.lean` does for the
1984 chapter, with page numbers).

| Category | In the paper | In CogLib now | Status |
|---|---|---|---|
| Representation | B-bit states; Hamming distance | `Cog.Item := List Bool`; `Cog.mismatches` | exists |
| Representation | operators with don't-cares | — | new (local to the theory) |
| Mechanism | problem-space search | `Cog.Space`, decision cycle `step`/`run`, `MEA` (`Process/ProblemSolving`) | exists; `Procedure` is deterministic + repairs |
| Mechanism | the r-decision procedure: a *distribution* over applicable operators | — | new; a stochastic policy `S → Dist O` would generalize the decision cycle |
| Mechanism | chunking: add the operator generalizing the solution | — (`ProblemSolving.lean` lists Soar chunking as "not yet here") | new; a candidate general process |
| Phenomenon | the power law of practice | `Phenomena/LearningCurve`: `Improves`, `DiminishingReturns`, `DiminishingRelativeReturns`, `ScaleRatio`, `ApproxScaleRatio`, `ShiftRatio` | exists, graded |
| Phenomenon | the fan effect: performance worsens with practice over a range | — | new, theory-neutral: `Worsens T lo hi` (∃ n, T n < T (n+1)) or a non-monotone predicate |
| Condition | regime r; sparsity; which games are drawn; test schedule | — | conditions of theorems, stated per result |
| Idealization | random graph → regular tree → 1-D biased walk | — | a stated approximation, not a mechanism: the seam (§3) |
| Library fact | hitting time of a biased walk on {0..D} (Eq. 2) and its regimes | — (cf. the harmonic-number lemmas in `Process/Practice`) | new mathematics, theory-neutral |
| Result at a setting | Fig. 1 | — | `Sims/`, later |
| Class-level claim | power law for any operator addition in the right regime | the class-theorem idiom (`…_of_laws`) | the natural CogLean form of the paper |

Two existing pieces matter most. `Phenomena/LearningCurve` was built so that a mechanism can be
shown to have some signatures of a power law and not others, and `Process/Practice` already
holds ACT-R's base-level practice curves to those predicates. SHH88 is a second theory of the
same phenomenon, and can be held to the same predicates without any new phenomenon work.

## 3. The shape: two tiers and a seam

**The executable tier** is the bit game as a theory package: states, don't-care operators,
`applicable`, the r-procedure as a `Dist` over successors, chunking after a trial. Cheap exact
theorems live here:
- at r = 1 the number of steps equals the Hamming distance (`optimal_steps_eq_hamming`);
- the chunked operator solves its own game in one step (`chunk_solves_in_one`) and adds 2^k
  edges (`chunk_adds_edges`); the initial operators connect any two states
  (`hypercube_connected`);
- a fan-effect witness: on a 2- or 3-bit game, at some r, adding an operator *raises* the
  expected steps (or lowers the probability of solving within k steps). This is the fan effect
  at the level of mechanism, proved rather than plotted.

**The theory tier** is the one-dimensional walk: `expectedSteps P D : Rat` by its recurrence,
the closed form (Eq. 2) proved by induction, and its monotonicities: fewer steps with a better
decision procedure (decreasing in P₋ for fixed D), more with a longer diameter, drift and
diffusion bounds (Eqs. 3–4). The fan-effect trade-off is a theorem about pairs (D, μ) → (D′, μ′)
with D′ ≤ D and μ′ > μ at which s increases. This is pure mathematics and theory-neutral; it
belongs in CogLib as a library fact once a second theory wants it.

**The seam** between the tiers is "the bit game behaves like the walk": an approximation, not
an equivalence. In the paper it is three sentences of idealization (uniform branching, one good
move per node, long cycles). Formalizing both tiers is what lets those assumptions be stated as
hypotheses, and lets one ask on which games and at which sizes they hold. That is an unstated
assumption made explicit, which is what the Intro paper says CogLean is for. It is a bridge in
the sense of the Intro's Appendix A, between two formal descriptions, but one that is justified
by approximation rather than proved as an equivalence.

## 4. A result that is probably waiting

In the drift regime the paper's own theory gives s ≈ ln n / ln μ (Eq. 6), and μ grows roughly
linearly with trials, since each trial adds a bounded number of edges. So the analytic
prediction is a *logarithmic* curve in trials, not a power law; it looks straight on a log-log
plot over the single decade Figure 1 spans. This is exactly the situation the library already
found for ACT-R's base level under spaced practice: `Cog.Act.spaced_looks_like_powerLaw` (within
7.5% of a power law over trials 1–8) against `Cog.Act.spaced_not_powerLaw` (not approximately a
power law over long ranges, for any exponent). A formalization of SHH88 would likely prove
`ApproxScaleRatio` on a range and the failure of `ScaleRatio` asymptotically, for the same
reason, and would say so about one of the two "power laws" the 1988 paper reports. That is a
result about the paper of the same kind as the peaking condition found in the 1984 chapter
(`SC.peaking_can_raise_overt_use`): not that the model is wrong, but that a claim its authors
drew from it needs a qualification they did not state.

The fan effect is the other half, and it is a phenomenon the power-law predicates cannot
express: a curve that goes up. Stated once as a predicate, it becomes a column that ACT-R's
base level, which is monotone, can *never* have, and that the graph-dynamic model has at some
r. That is the beginning of a **practice matrix**: SHH88 and ACT-R's base level (and, later,
Rosenbloom's chunking and ACT*'s strengthening) against `Improves`, `DiminishingRelativeReturns`,
`ScaleRatio`, `ApproxScaleRatio` and `Worsens`, built the way the memory matrix was. It is the
comparison the paper's own last paragraph makes in prose.

## 5. Blending into CogLib without disturbing it

Follow `notes/LAYERING_POLICY.md` literally:
1. **A theory package first** (`GraphDynamics/`, namespace `GD`, requires CogLib), with
   everything new written locally: operators, the policy, chunking, the walk lemmas, the
   witnesses. Nothing in CogLib changes.
2. **Promote later, and only what is theory-neutral and wanted by a second theory.** The
   candidates are already visible: the fan-effect predicate (into `Phenomena/LearningCurve`); a
   stochastic policy for problem spaces (`S → Dist O`, generalizing `Procedure`); chunking as a
   process; the hitting-time lemma. The audit's "promotion candidates" section flags exactly
   these when a second user appears.
3. **Treat the idealization as a postulate of the theory tier,** stated and cited, not derived.
   Random-graph theory is out of scope; the paper itself assumes its way from the random graph
   to the regular tree.
4. **Sims last.** The 5-bit curves of Figure 1 are a `Sims/` program, run after the theorems,
   and reconciled with them (as `sc-check` reconciles the DOA sampler with `SC.trial`).

## 6. Decisions to make early

- **Expected steps is an unbounded random variable,** and `Cog.Dist` is finite. Options: a
  finite horizon ("solved within k steps", a `Dist` by k-fold `bind`, matching the library's
  idiom); or the exact expected hitting time on the game's state graph by solving the linear
  system over `Rat` (exact, but heavy for the kernel beyond a few states). The 1-D theory tier
  needs neither: its recurrence has a closed form.
- **Logarithms.** D = ln n / ln μ and the asymptotic power-law question need real numbers; the
  lab confines Mathlib to `ACTR/`. Either a second Mathlib package, or a rational stand-in
  (D as an integer logarithm, which core Lean can compute) for everything but the asymptotics.
- **Fidelity of the decision procedure.** The paper's r-procedure is itself "only heuristic";
  the formalization can state it exactly as written and prove its relation to the Hamming
  heuristic, rather than to optimal search.
- **Which performance measure.** Steps (the paper), or a finite-horizon solve probability.
  Both can be held to the curve predicates; say which.

## 7. Suggested order, when taken up

1. The postulate table, as a Lean module header with page numbers (P1 states and operators;
   P2 the initial hypercube; P3 the r-procedure; P4 chunking; I1 the idealization; conditions).
2. The theory tier: `expectedSteps`, Eq. 2, monotonicities, the regimes, the fan-effect
   trade-off witness, and the log-versus-power-law result on the drift regime.
3. The executable tier: the bit game, `optimal_steps_eq_hamming`, `chunk_solves_in_one`,
   `chunk_adds_edges`, a 2- or 3-bit fan-effect witness by `decide +kernel`.
4. The practice matrix row: SHH88's curves against the `LearningCurve` predicates and
   `Worsens`, beside `Cog.Act.spaced`/`massed`.
5. `Sims/`: the 5-bit Figure 1, and a check of the sampler against the exact small cases.
6. Promotions to CogLib, each a separate commit, after the audit flags them.
