/-
The distributions-of-associations model of strategy choice (Siegler &
Shrager 1984), as choices from CogLib.

Siegler, R. S., & Shrager, J. (1984). Strategy choices in addition and
subtraction: How do children know what to do? In C. Sophian (Ed.), *Origins
of cognitive skills* (pp. 229-293). Hillsdale, NJ: Erlbaum. Page numbers
below are the chapter's.

| Postulate | CogLib |
|---|---|
| A1 Representation: "associations of varying strengths between each problem and possible answers" (p. 238) | strengths `Answer → Rat` over a list of answers |
| A2 Parameters: "the child sets two parameters: a confidence criterion and a search length" (p. 239) | the `cc` and `n` of `Cog.search` |
| A3 Retrieval: "the probability of any given answer's being retrieved ... is proportional to [its] associative strength"; stated "if [its] associative strength exceeds the confidence criterion"; repeated up to the search length (p. 240) | `Cog.sample`, `Cog.above`, `Cog.search` |
| A4 Elaboration: putting up fingers adds an association to the answer equal to the number of objects; the new strengths are the sums divided by one plus the added strength (p. 242, fn. 4); one more retrieval | `elaborate`, then `Cog.sample` once |
| A5 Counting: count the objects and state the last number; each count can skip an object or count it twice, with fixed probabilities (p. 273, item 5) | `count` |
| A6 Learning: "every time the system advances an answer, the association between that answer and the problem increases"; twice as much for correct answers (p. 273, item 6) | not yet stated |

Simplifications:
* Only the three strategies of the chapter's simulation: retrieval, fingers,
  counting fingers. Counting from an internal representation (pp. 242-243) is
  not modelled, as in the simulation (p. 276).
* The confidence criterion and search length are parameters of a trial. The
  simulation draws them at random (p. 273, item 2); averaging over them is
  left to the experiments.
* The elaborated representation always holds the right number of objects,
  so the elaborated retrieval is primed at the correct sum.
-/

import CogLib

namespace SC

open Cog Dist

/-- Answers are numbers. -/
abbrev Answer := Nat

/-- An addition problem `a + b`. -/
structure Problem where
  a : Nat
  b : Nat
  deriving Repr, DecidableEq

/-- The correct answer, and the number of objects in the elaborated
representation. -/
def Problem.sum (p : Problem) : Nat := p.a + p.b

/-- The strategies of the simulation (p. 276). -/
inductive Strategy where
  | retrieval
  | fingers
  | countingFingers
  deriving Repr, DecidableEq

/-- **A4 Elaboration.** Representing `objects` objects (on the fingers) adds
strength `e` to that answer; the result is renormalized by `1 + e`. -/
def elaborate (s : Answer → Rat) (objects : Nat) (e : Rat) : Answer → Rat :=
  fun a => (s a + if a = objects then e else 0) / (1 + e)

/-- **A5 Counting.** Counting `k` objects, each is skipped with probability
`qs`, counted twice with probability `qd`, and otherwise counted once. The
result is the last number counted. -/
def count (qs qd : Rat) : Nat → Dist Nat
  | 0 => Dist.pure 0
  | k + 1 => Dist.bind (count qs qd k) fun r => [(r, qs), (r + 1, 1 - qs - qd), (r + 2, qd)]

/-- The parameters of the backup strategies: the strength added by
elaboration (`.05` in the simulation, p. 242 fn. 4) and the counting errors. -/
structure Backup where
  e : Rat
  qs : Rat
  qd : Rat

/-- **The backup strategies** (A4, A5). Put up fingers and retrieve once more
from the elaborated strengths; if that fails too, count the fingers. -/
def backup (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat) (p : Problem) :
    Dist (Strategy × Answer) :=
  Dist.bind (sample as (elaborate s p.sum bk.e)) fun a =>
    if above (elaborate s p.sum bk.e) cc a then Dist.pure (.fingers, a)
    else Dist.bind (count bk.qs bk.qd p.sum) fun r => Dist.pure (.countingFingers, r)

/-- **A trial** (Fig. 9.2B). Retrieve, with confidence criterion `cc` and
search length `n` (A2, A3); if nothing is stated, use the backup strategies.
The result is the strategy used and the answer stated. -/
def trial (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat) (n : Nat)
    (p : Problem) : Dist (Strategy × Answer) :=
  Dist.bind (search as s cc 0 n) fun
    | .stated a _ => Dist.pure (.retrieval, a)
    | .exhausted => backup as s bk cc p

/-! ### Events -/

def isRetrieval (x : Strategy × Answer) : Bool := x.1 == .retrieval

def isCounting (x : Strategy × Answer) : Bool := x.1 == .countingFingers

/-- A wrong answer stated by retrieval. -/
def retrievalWrong (p : Problem) (x : Strategy × Answer) : Bool :=
  x.1 == .retrieval && x.2 != p.sum

/-- A wrong answer stated by counting. -/
def countingWrong (p : Problem) (x : Strategy × Answer) : Bool :=
  x.1 == .countingFingers && x.2 != p.sum

end SC
