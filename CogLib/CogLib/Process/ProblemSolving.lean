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

Main results: means-ends analysis is sound for every space: whenever it
succeeds, the goal holds (`achieve_sound`). Runs can be traced, with each
operator applied and each impasse with its repair (`runTrace`), and
forgetting the trace gives the run (`runTrace_forget`). An impasse arises
only where a proposed operator's precondition fails (`step_impasse_iff`);
with no impasse, a step is just the operator's effect (`step_no_impasse`):
these two are restatements of the definitions.
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

/-! ### What means-ends analysis guarantees -/

/-- Every successful outcome of a distribution satisfies `P`. -/
def AllSome (P : S → Prop) (d : Dist (Option S)) : Prop :=
  ∀ x ∈ d, ∀ s, x.1 = some s → P s

theorem allSome_pure_none (P : S → Prop) : AllSome P (Dist.pure none) := by
  intro x hx s hs
  simp [Dist.pure] at hx
  rw [hx] at hs
  cases hs

theorem allSome_pure_some (P : S → Prop) (s : S) (h : P s) : AllSome P (Dist.pure (some s)) := by
  intro x hx s' hs
  simp [Dist.pure] at hx
  rw [hx] at hs
  cases hs
  exact h

theorem mem_bind {α β : Type} (d : Dist α) (f : α → Dist β) (x : β × Rat) (hx : x ∈ Dist.bind d f) :
    ∃ y ∈ d, ∃ z ∈ f y.1, x.1 = z.1 := by
  induction d with
  | nil => simp [Dist.bind] at hx
  | cons y d ih =>
    obtain ⟨a, p⟩ := y
    simp only [Dist.bind, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨z, hz, rfl⟩ | hx
    · exact ⟨(a, p), List.mem_cons_self, z, hz, rfl⟩
    · obtain ⟨y, hy, z, hz, h⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, z, hz, h⟩

theorem allSome_bind {α : Type} (P : S → Prop) (d : Dist α) (f : α → Dist (Option S))
    (h : ∀ y ∈ d, AllSome P (f y.1)) : AllSome P (Dist.bind d f) := by
  intro x hx s hs
  obtain ⟨y, hy, z, hz, hxz⟩ := mem_bind d f x hx
  exact h y hy z hz s (hxz ▸ hs)

theorem allSome_orElse (P : S → Prop) (d alt : Dist (Option S)) (hd : AllSome P d)
    (ha : AllSome P alt) : AllSome P (orElse d alt) := by
  unfold orElse
  apply allSome_bind
  intro y hy
  match hy1 : y.1 with
  | some s => exact allSome_pure_some P s (hd y hy s hy1)
  | none => exact ha

/-- **Means-ends analysis is sound**, for every problem space, difference
table and depth: every outcome in which it succeeds satisfies the goal. -/
theorem achieve_sound (Sp : Space S O) (M : MEA S O C) (k : Nat) (goal : List C) (s : S) :
    AllSome (fun s' => ∀ c ∈ goal, M.holds c s' = true) (achieve Sp M k goal s) := by
  induction k generalizing goal s with
  | zero => exact allSome_pure_none _
  | succ k ih =>
    unfold achieve
    split
    · rename_i hf
      apply allSome_pure_some
      intro c hc
      have := List.find?_eq_none.mp hf c hc
      simpa using this
    · rename_i c _
      induction M.table c with
      | nil => exact allSome_pure_none _
      | cons o os ihos =>
        simp only [List.foldr_cons]
        apply allSome_orElse _ _ _ _ ihos
        apply allSome_bind
        intro y _
        match y.1 with
        | none => exact allSome_pure_none _
        | some s1 =>
          simp only
          split
          · apply allSome_bind
            intro z _
            exact ih goal z.1
          · exact allSome_pure_none _

/-! ### How means-ends analysis chains -/

theorem orElse_pure_some (s : S) (alt : Dist (Option S)) :
    orElse (Dist.pure (some s)) alt = Dist.pure (some s) := by
  simp [orElse, Dist.bind_pure_left]

theorem orElse_pure_none (alt : Dist (Option S)) : orElse (Dist.pure none) alt = alt := by
  simp [orElse, Dist.bind_pure_left]

/-- With every condition of the goal met, it is achieved at once. -/
theorem achieve_done (Sp : Space S O) (M : MEA S O C) (k : Nat) (goal : List C) (s : S)
    (h : goal.find? (fun c => !M.holds c s) = none) : achieve Sp M (k + 1) goal s = Dist.pure (some s) := by
  simp [achieve, h]

/-- **A link of a chain.** If the first unmet condition has a single relevant
operator, its preconditions are achieved (state `s1`), and it then applies
deterministically (state `s2`), achieving the goal goes on from `s2`. -/
theorem achieve_chain_step (Sp : Space S O) (M : MEA S O C) (k : Nat) (goal : List C) (s s1 s2 : S)
    (c : C) (o : O) (cs : List C) (hf : goal.find? (fun c => !M.holds c s) = some c)
    (ht : M.table c = [o]) (hc : M.conds o = cs)
    (hsub : achieve Sp M k cs s = Dist.pure (some s1)) (hpre : Sp.pre o s1 = true)
    (happ : Sp.apply o s1 = Dist.pure s2) :
    achieve Sp M (k + 1) goal s = achieve Sp M k goal s2 := by
  simp only [achieve, hf, ht, hc, List.foldr_cons, List.foldr_nil, hsub, Dist.bind_pure_left, hpre,
    ite_true, happ]
  unfold orElse
  conv => rhs; rw [← Dist.bind_pure_right (achieve Sp M k goal s2)]
  apply Dist.bind_congr
  intro r
  match r with
  | some _ => rfl
  | none => rfl

/-- **A broken link.** If the single relevant operator's preconditions cannot
be achieved, the goal fails. -/
theorem achieve_chain_fail_sub (Sp : Space S O) (M : MEA S O C) (k : Nat) (goal : List C) (s : S)
    (c : C) (o : O) (cs : List C) (hf : goal.find? (fun c => !M.holds c s) = some c)
    (ht : M.table c = [o]) (hc : M.conds o = cs) (hsub : achieve Sp M k cs s = Dist.pure none) :
    achieve Sp M (k + 1) goal s = Dist.pure none := by
  simp [achieve, hf, ht, hc, hsub, Dist.bind_pure_left, orElse_pure_none]

/-- **A broken link.** If, once its preconditions are achieved, the single
relevant operator still does not apply, the goal fails. -/
theorem achieve_chain_fail_pre (Sp : Space S O) (M : MEA S O C) (k : Nat) (goal : List C) (s s1 : S)
    (c : C) (o : O) (cs : List C) (hf : goal.find? (fun c => !M.holds c s) = some c)
    (ht : M.table c = [o]) (hc : M.conds o = cs)
    (hsub : achieve Sp M k cs s = Dist.pure (some s1)) (hpre : Sp.pre o s1 = false) :
    achieve Sp M (k + 1) goal s = Dist.pure none := by
  simp [achieve, hf, ht, hc, hsub, Dist.bind_pure_left, hpre, orElse_pure_none]

/-! ### Traces: what the solver did, as an observable -/

/-- One event of a run: an operator applied, or an impasse at an operator and
the repair taken. -/
inductive Event (O : Type) where
  | applied (o : O)
  | repaired (stuck r : O)

/-- One decision cycle, with what happened. -/
def stepTrace (Sp : Space S O) (P : Procedure S O) (R : Repairer S O) (s : S) :
    Dist (Option (S × Event O)) :=
  match P s with
  | none => Dist.pure none
  | some o =>
    if Sp.pre o s then Dist.bind (Sp.apply o s) fun s' => Dist.pure (some (s', .applied o))
    else match validRepairs Sp R o s with
      | [] => Dist.pure none
      | rs => Dist.bind (uniformOf rs) fun r => Dist.bind (Sp.apply r s) fun s' =>
          Dist.pure (some (s', .repaired o r))

/-- **A run with its trace**: the final state, and the events in order. -/
def runTrace (Sp : Space S O) (P : Procedure S O) (R : Repairer S O) : Nat → S → Dist (S × List (Event O))
  | 0, s => Dist.pure (s, [])
  | k + 1, s => Dist.bind (stepTrace Sp P R s) fun r => match r with
    | none => Dist.pure (s, [])
    | some (s', e) => Dist.bind (runTrace Sp P R k s') fun (s'', es) => Dist.pure (s'', e :: es)

theorem stepTrace_forget (Sp : Space S O) (P : Procedure S O) (R : Repairer S O) (s : S) :
    Dist.bind (stepTrace Sp P R s) (fun r => Dist.pure (r.map Prod.fst)) = step Sp P R s := by
  unfold stepTrace step
  split
  · simp [Dist.bind_pure_left]
  · split
    · simp only [Dist.bind_assoc, Dist.bind_pure_left, Option.map_some]
    · split <;> simp only [Dist.bind_assoc, Dist.bind_pure_left, Option.map_some, Option.map_none]

/-- **Forgetting the trace gives the run.** -/
theorem runTrace_forget (Sp : Space S O) (P : Procedure S O) (R : Repairer S O) (k : Nat) (s : S) :
    Dist.bind (runTrace Sp P R k s) (fun x => Dist.pure x.1) = run Sp P R k s := by
  induction k generalizing s with
  | zero => simp [runTrace, run, Dist.bind_pure_left]
  | succ k ih =>
    simp only [runTrace, run]
    rw [← stepTrace_forget Sp P R s, Dist.bind_assoc, Dist.bind_assoc]
    apply Dist.bind_congr
    intro r
    match r with
    | none => simp [Dist.bind_pure_left]
    | some (s', e) =>
      simp only [Dist.bind_assoc, Dist.bind_pure_left, Option.map_some]
      rw [← ih s']

end Cog
