# Preregistration: what the Lean model predicts for the blind simulation

This file is written and committed before the simulator exists. It fixes the checks that `compare.py` will run on the simulator's logs (`SPEC.md` §9.3), and how each is judged. The implementer does not see this file.

## Setup

- **Instances.** `compare.py` generates random instances:
  - encoding: `bcd` or `rich`;
  - noticing order: a named one, or a random permutation of all the encoding's features;
  - 2–8 familiar problems, some sets structured (sharing hundreds digits, round problems, neighbours such as 700+100 and 800+100);
  - schedules: the familiar problems, near neighbours (one digit changed), commuted problems and random problems;
  - whole-problem strengths: random, sometimes sharp (only the stored problem's sum above c);
  - c ∈ {1/10, 1/4, 1/2}, n ∈ {1, 2, 3};
  - random single-digit strengths, elab, qs, qd.

  There are also the fixed instances in `instances/`, matching the Lean exports.
- **Fixed mode** (learning off): the net and the strengths stay fixed. This is where Predictions 1–6, 9–10 and 13–18 are checked.
- **Learning mode**: Predictions 7, 11 and 12.
- **Non-vacuity.** For every exact check, the report gives how many trials met its hypothesis. A check whose hypothesis was never met is reported as *vacuous*, not as passed.

Notation, for a trial on x recognized as y:
- s_y: y's whole-problem strengths, with total T_y;
- R_y = Σ_{a : s_y(a) > c} s_y(a) / T_y;
- Gₙ = 1 + (1 − R_y) + … + (1 − R_y)ⁿ⁻¹.

## Tolerance

- **Exact checks**: zero violations allowed, over all trials.
- **Probabilities**: a frequency p̂ from N trials, against a predicted p.
  - If p = 0 or p = 1, the count must be exactly 0 or N.
  - Otherwise accept when |p̂ − p| ≤ 4·√(p(1 − p)/N).

## Checks

| # | Lean | Kind | Hypothesis (from the log and the instance) | Prediction |
|---|---|---|---|---|
| L-A | `Net.confusion_agrees_on_path` | exact | x recognized as y ≠ x | the codes of x and y agree on every feature in `path` |
| P1 | `MD.columns_prob` | prob | x not recognized / recognized as y | columns-route frequency = 1 / (1 − R_y)ⁿ |
| P2 | `MD.whole_depends_only_on_route` | prob | x recognized as y; each answer a | frequency of (whole, a) = [s_y(a) > c] · s_y(a)/T_y · Gₙ |
| P2′ | same | prob | x, x′ recognized as the same y | the same whole-route answer distribution (two-sample, same 4σ rule on the pooled p) |
| P3 | `MD.confusion_gives_neighbours_answer` | exact | x recognized as y, y sharp | every whole-route answer is y's sum |
| P4 | `MD.confident_errors` | prob | as P3, x.sum ≠ y.sum | whole-wrong frequency = whole frequency on x; columns frequency on x = columns frequency on y (both = (1 − R_y)ⁿ) |
| P5 | `MD.same_sum_confusion_harmless` | prob | x recognized as y, x.sum = y.sum (e.g. commuted) | whole-wrong frequency on x = on y |
| P6a | `MD.near_miss_200` | exact | x recognized as y; `path` contains the digit features (bcd: 4 bits; rich: 9 thresholds) of both hundreds digits | \|y.sum − x.sum\| < 200 |
| P6b | `MD.near_miss_20` | exact | also the tens digits' features | \|y.sum − x.sum\| < 20 |
| P9 | `MD.columns_place_value` | exact | columns route | answer = r0 + 10·r1 + 100·r2 (logged column answers) |
| P10a | `MD.one_column_errs` | exact | columns route, exactly one column wrong (by δ, at place 10ʲ) | answer wrong, and answer − sum = δ·10ʲ |
| P10b | `MD.doaFact_wrong` | prob | all column additions of digits d + e | wrong frequency = the exact single-digit DOA error probability (computed by `compare.py` from the parameters) |
| P13 | `MD.confusion_keeps_zeros` | exact | rich; x recognized as y; a zero flag on `path` | that digit is 0 in x iff in y |
| P14 | `MD.round_confusion_exact` | exact | rich; y round; `path` has the zero flags of both tens and units, and the hundreds thresholds | x = y |
| P15 | `MD.confusion_within_gap` | exact | rich; thresholds lo < hi of one digit on `path`, y's digit in (lo, hi] | x's digit in (lo, hi] |
| P17 | `MD.facts_same_sum` | exact | rich; all 300 column-fact features on `path` | x.sum = y.sum |
| P18 | `MD.facts_mod_100`, `facts_mod_10` | exact | rich; all fact features of tens and units (or units) on `path` | x.sum ≡ y.sum mod 100 (mod 10) |
| P7 | `MD.learning_preserves_trial` | exact | learning mode; q recognized as itself at some trial | q recognized as itself at every later trial |
| P11 | `MD.discrimination_removes_confusion` | exact | learning mode; `net_learned` after a trial on x confused with y | from then on x is recognized as x, and y is still recognized as y |
| P12 | `MD.discrimination_then_columns` | exact, conditional | as P11, and the implementer's O2 gives the new problem no strength above c | x's next trial (before any strengthening of x) goes by the columns |
| Lean-exact | `#eval` of `MD.trial` | prob | the instances in `instances/` | each (route, answer) frequency = Lean's exact probability; `recognized_as` as in Lean |

## Expected in advance

- **P17 and P18 will probably be vacuous on rich instances.** A one-hot fact is fixed by any single feature that reads 1, but EPAM grows one test per confusion, so a path will hardly ever contain all 100 features of a column. The Lean theorems are true but weak for this encoding. A stronger law ("the features of the fact that read 1 on the path determine it") would apply. If they come out vacuous, that is recorded as a finding about the theorems, not as a pass.
- **P12 depends on O2.** If the implementer gives new problems strengths above c, P12 doesn't apply, and that is reported.
- **Learning mode beyond P7, P11 and P12 is exploratory.** It will report the sequences on each problem first answered wrongly by the whole route: confident error → columns → whole and correct. It also reports how often each occurs and how long each phase lasts. No values are predicted.

## Diagnosis of failures

Each failure is classified as one of:
- an implementation bug: the simulator departs from SPEC;
- a spec ambiguity: SPEC allows the simulator's reading, which the Lean model excludes;
- formalization drift: SPEC and the simulator agree, and the Lean model says something else.

Only the last two go into `OPEN_ISSUES.md`.
