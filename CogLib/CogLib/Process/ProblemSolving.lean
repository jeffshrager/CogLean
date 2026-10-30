/-
Processes: problem solving in a problem space, under two control regimes.

A problem space (Newell & Simon 1972) has states and operators; each
operator has preconditions and an effect. An effect is a distribution over
states, so an operator can include a probabilistic process, such as
retrieving a fact.

**Means-ends analysis** (GPS; Newell, Shaw & Simon 1959). Goals are lists
of conditions. To achieve a goal, find the first condition that does not
hold (the most important difference); take the operators relevant to it
from the difference table, in order; for each, first achieve its
preconditions (a subgoal), then apply it, then continue with the goal. If an
operator fails, back up and try the next (backtracking). Bounded by a depth.
Not yet here: GPS's ordering of differences by difficulty beyond list order,
and Soar's tie and conflict impasses and chunking.

**The decision cycle with impasses** (the side of Soar and of repair
theory; Brown & VanLehn 1980). Rules propose an operator for the current
state. If none is proposed, the problem is done or abandoned; if the
proposed operator's precondition is violated, that is an *impasse*. A local
problem solver then repairs it: repair heuristics propose actions in its
place, critics veto some, and one of the survivors is taken at random.

Main results: an impasse arises only where a proposed operator's
precondition fails (`step_impasse_iff`); with no impasse, a step is just
the operator's effect (`step_no_impasse`).
-/

import CogLib.Rep.Distribution

namespace Cog

variable {S O C : Type}

/-- A problem space: operators with preconditions and effects. -/
structure Space (S O : Type) where
  pre : O → S → Bool
  apply : O → S → Dist S

/-! ### Means-ends analysis (GPS) -/

/-- The parts of means-ends analysis: when a condition holds, which
operators are relevant to it (the difference table), and each operator's
preconditions as conditions. -/
structure MEA (S O C : Type) where
  holds : C → S → Bool
  table : C → List O
  conds : O → List C

/-- Try alternatives in turn: if the first fails (`none`) on some outcome,
back up and try the next there. -/
def orElse (d : Dist (Option S)) (alt : Dist (Option S)) : Dist (Option S) :=
  Dist.bind d fun r => match r with
    | some s => Dist.pure (some s)
    | none => alt

/-- **Achieve a goal** (a list of conditions) by means-ends analysis: the
first unmet condition; its relevant operators in order, each tried by first
achieving its preconditions (a subgoal), then applying it, then continuing;
on failure, back up to the next operator. -/
def achieve (Sp : Space S O) (M : MEA S O C) : Nat → List C → S → Dist (Option S)
  | 0, _, _ => Dist.pure none
  | k + 1, goal, s =>
    match goal.find? fun c => !M.holds c s with
    | none => Dist.pure (some s)
    | some c => (M.table c).foldr (fun o alt => orElse
        (Dist.bind (achieve Sp M k (M.conds o) s) fun r => match r with
          | none => Dist.pure none
          | some s1 => if Sp.pre o s1 then
              Dist.bind (Sp.apply o s1) fun s2 => achieve Sp M k goal s2
            else Dist.pure none)
        alt) (Dist.pure none)

/-! ### The decision cycle, with impasses and repairs -/

/-- A procedure: rules propose the next operator (or none: stop). -/
abbrev Procedure (S O : Type) := S → Option O

/-- Repair: heuristics propose replacement operators for a stuck one; critics
veto some. -/
structure Repairer (S O : Type) where
  heuristics : O → S → List O
  critic : O → S → Bool

/-- The repairs that survive: preconditions met and no critic violated. -/
def validRepairs (Sp : Space S O) (R : Repairer S O) (o : O) (s : S) : List O :=
  (R.heuristics o s).filter fun r => Sp.pre r s && !R.critic r s

/-- A uniform choice. -/
def uniformOf {α : Type} (xs : List α) : Dist α := xs.map fun x => (x, 1 / (xs.length : Rat))

/-- One decision cycle: apply the proposed operator; at an impasse, a valid
repair chosen at random. `none` means nothing to do (finished, or no
valid repair: the problem is abandoned there). -/
def step (Sp : Space S O) (P : Procedure S O) (R : Repairer S O) (s : S) : Dist (Option S) :=
  match P s with
  | none => Dist.pure none
  | some o =>
    if Sp.pre o s then Dist.bind (Sp.apply o s) fun s' => Dist.pure (some s')
    else match validRepairs Sp R o s with
      | [] => Dist.pure none
      | rs => Dist.bind (uniformOf rs) fun r => Dist.bind (Sp.apply r s) fun s' => Dist.pure (some s')

/-- Run the decision cycle for at most `k` steps; the final states. -/
def run (Sp : Space S O) (P : Procedure S O) (R : Repairer S O) : Nat → S → Dist S
  | 0, s => Dist.pure s
  | k + 1, s => Dist.bind (step Sp P R s) fun r => match r with
    | none => Dist.pure s
    | some s' => run Sp P R k s'

/-- Whether the next step is at an impasse. -/
def AtImpasse (Sp : Space S O) (P : Procedure S O) (s : S) : Prop :=
  ∃ o, P s = some o ∧ Sp.pre o s = false

/-- **An impasse is a proposed operator whose precondition fails.** -/
theorem step_impasse_iff (Sp : Space S O) (P : Procedure S O) (s : S) :
    AtImpasse Sp P s ↔ ∃ o, P s = some o ∧ ¬ Sp.pre o s = true := by
  simp [AtImpasse]

/-- **With no impasse, a step is the operator's effect.** -/
theorem step_no_impasse (Sp : Space S O) (P : Procedure S O) (R : Repairer S O) (s : S) (o : O)
    (hp : P s = some o) (hpre : Sp.pre o s = true) :
    step Sp P R s = Dist.bind (Sp.apply o s) fun s' => Dist.pure (some s') := by
  simp [step, hp, hpre]

end Cog
