/-
Memory structures: declarative memory with activation (ACT-R).

A chunk is a stored code with the times it was used. Each use adds to the
chunk's activation, and each use's contribution decays with time. A probe
retrieves a chunk with a probability that rises with the chunk's activation
and falls with each feature on which chunk and probe mismatch (partial
matching). Retrieval can also fail.

This is ACT-R's Boltzmann (softmax) retrieval rule, `P(i) ∝ e^{A_i/s}`, with
failure weight `e^{τ/s}`, for decay `d = 1` and temperature `s = 1`. Then
`e^{A_i} = (Σ_k 1/(t - t_k)) · μ^{m_i}`, with `μ = e^{-P}` for mismatch
penalty `P`, and `m_i` the number of mismatching features. The failure weight
is `θ = e^τ`. Every quantity is rational. Other decay rates and temperatures
need real exponentials.

Results:
* `Act.prob_retrieve`: a retrieval event's probability is its share of the
  total weight.
* `Act.retrieve_not_certain`: no probe retrieves a stored chunk for certain.
* `actRetriever_stableRetrieval`: so stable retrieval holds, but only
  vacuously: its hypothesis is never met.
* `Act.latency`: retrieval time `F · e^{-A}` from the base level; its
  practice curves are in `Process/Practice`.
* `Act.retrieveIn`: retrieval in a context that primes chunks (spreading
  activation, as a factor on a chunk's weight); `Act.retrieveIn_unprimed`,
  `Act.prob_primed`.
* `Act.retrieve_rehearse`: seeing `y` just before the test is priming `y`, by
  `1 + k j / B`, derived from the base level.
-/

import CogLib.Rep.Distribution
import CogLib.Rep.Features
import CogLib.Phenomena.RetrievalLaws

namespace Cog

/-- A moment on the memory clock, in steps. -/
abbrev Time := Nat

/-- A chunk: a stored code, and the times it was used. -/
structure Chunk where
  code : Item
  uses : List Time
  deriving Repr, DecidableEq

/-- Declarative memory: the current time, and the chunks. -/
structure ActState where
  now : Time
  chunks : List Chunk
  deriving Repr

/-- The parameters of retrieval: the features compared in partial matching,
the weight factor per mismatch `μ = e^{-P}`, and the failure weight
`θ = e^τ`. -/
structure ActParams where
  fs : List Feature
  mu : Rat
  theta : Rat

namespace Act

open Dist

/-- `e^B` for base-level activation `B = ln Σ_k (now - t_k)^{-1}`. -/
def baseWeight (now : Time) (uses : List Time) : Rat :=
  (uses.map fun t => 1 / ((now - t : Nat) : Rat)).sum

/-- **Latency**, ACT-R's retrieval-time rule `F · e^{-A}`, for a chunk
retrieved by an exact match, so that its activation is its base level: with
decay 1, `F / e^B`. -/
def latency (F : Rat) (now : Time) (uses : List Time) : Rat := F / baseWeight now uses

/-- `e^A` for a chunk's activation `A` given the probe `x`. -/
def chunkWeight (P : ActParams) (now : Time) (x : Item) (c : Chunk) : Rat :=
  baseWeight now c.uses * P.mu ^ mismatches P.fs x c.code

/-- What retrieval can produce: failure, or a stored code. -/
def outcomes (s : ActState) : List (Option Item) := none :: s.chunks.map fun c => some c.code

/-- The weight of each outcome for the probe `x`. -/
def weight (P : ActParams) (s : ActState) (x : Item) : Option Item → Rat
  | none => P.theta
  | some y => ((s.chunks.filter fun c => c.code == y).map (chunkWeight P s.now x)).sum

/-- **Retrieval**: an outcome in proportion to its weight. -/
def retrieve (P : ActParams) (s : ActState) (x : Item) : Dist (Option Item) :=
  Dist.sample (outcomes s) (weight P s x)

/-- Record a use of `x` at time `t`: on its chunk, or on a new one. -/
def addUse (t : Time) (x : Item) : List Chunk → List Chunk
  | [] => [⟨x, [t]⟩]
  | c :: cs => if c.code = x then ⟨c.code, t :: c.uses⟩ :: cs else c :: addUse t x cs

/-- **Study**: a use of `x` now, then the clock advances. -/
def study (s : ActState) (x : Item) : ActState := ⟨s.now + 1, addUse s.now x s.chunks⟩

theorem prob_retrieve (P : ActParams) (s : ActState) (x : Item) (e : Option Item → Bool) :
    prob (retrieve P s x) e =
      strengthIn (outcomes s) (weight P s x) e / total (outcomes s) (weight P s x) :=
  prob_sample _ _ _

/-- **Retrieval is never certain.** Failure is always among the outcomes. -/
theorem retrieve_not_certain (P : ActParams) (s : ActState) (x y : Item) :
    retrieve P s x ≠ Dist.pure (some y) := by
  intro h
  simp [retrieve, Dist.sample, outcomes, Dist.pure] at h

/-! ### Priming

In ACT-R, spreading activation from the current context adds `S_i` to chunk
`i`'s activation, so it multiplies the chunk's weight by `e^{S_i}`. Here that
factor is a parameter, `prime y`, for the chunks with code `y` (1: not
primed); it can come from any account of the context, such as
`Process/SpreadingActivation`. Repetition priming, the boost from a recent
use, is already in the base level. -/

/-- The weight of each outcome for the probe `x`, in a context that primes
codes by `prime`. -/
def weightIn (P : ActParams) (prime : Item → Rat) (s : ActState) (x : Item) : Option Item → Rat
  | none => P.theta
  | some y => prime y * weight P s x (some y)

/-- **Retrieval in a priming context.** -/
def retrieveIn (P : ActParams) (prime : Item → Rat) (s : ActState) (x : Item) : Dist (Option Item) :=
  Dist.sample (outcomes s) (weightIn P prime s x)

/-- A context that primes the code `y` by the factor `ρ`, and nothing else. -/
def primeOnly (y : Item) (ρ : Rat) : Item → Rat := fun z => if z = y then ρ else 1

/-- With nothing primed, retrieval in context is plain retrieval. -/
theorem retrieveIn_unprimed (P : ActParams) (s : ActState) (x : Item) :
    retrieveIn P (fun _ => 1) s x = retrieve P s x := by
  have : weightIn P (fun _ => 1) s x = weight P s x := by
    funext o; cases o <;> simp [weightIn, weight]
  simp only [retrieveIn, retrieve, this]

theorem baseWeight_nonneg (now : Time) (uses : List Time) : 0 ≤ baseWeight now uses := by
  unfold baseWeight
  induction uses with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    have : 0 ≤ 1 / ((now - t : Nat) : Rat) := div_nonneg' (by decide +kernel) (Rat.natCast_nonneg)
    grind

/-- Weights are never negative, for nonnegative `μ` and `θ`. -/
theorem weight_nonneg (P : ActParams) (hμ : 0 ≤ P.mu) (hθ : 0 ≤ P.theta) (s : ActState) (x : Item) :
    ∀ o, 0 ≤ weight P s x o := by
  intro o
  cases o with
  | none => exact hθ
  | some y =>
    simp only [weight]
    generalize (s.chunks.filter fun c => c.code == y) = cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      have : 0 ≤ chunkWeight P s.now x c :=
        Rat.mul_nonneg (baseWeight_nonneg _ _) (Rat.pow_nonneg hμ)
      grind

/-- Priming `y` scales the weight on `y`, and leaves the rest. -/
theorem strengthIn_primed (as : List (Option Item)) (w : Option Item → Rat) (y : Item) (ρ : Rat) :
    strengthIn as (fun o => match o with | none => w none | some z => primeOnly y ρ z * w (some z))
        (· == some y) = ρ * strengthIn as w (· == some y) ∧
    strengthIn as (fun o => match o with | none => w none | some z => primeOnly y ρ z * w (some z))
        (fun o => !(o == some y)) = strengthIn as w (fun o => !(o == some y)) := by
  induction as with
  | nil => simp [strengthIn]
  | cons o as ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [strengthIn, ih1, ih2]
    cases o with
    | none => simp; grind
    | some z =>
      by_cases h : z = y
      · subst h; simp [primeOnly]; grind
      · simp [primeOnly, h]; grind

/-- The same, stated on `weightIn`. -/
theorem strengthIn_weightIn (P : ActParams) (s : ActState) (x y : Item) (ρ : Rat) :
    strengthIn (outcomes s) (weightIn P (primeOnly y ρ) s x) (· == some y) =
        ρ * strengthIn (outcomes s) (weight P s x) (· == some y) ∧
      strengthIn (outcomes s) (weightIn P (primeOnly y ρ) s x) (fun o => !(o == some y)) =
        strengthIn (outcomes s) (weight P s x) (fun o => !(o == some y)) := by
  have hw : weightIn P (primeOnly y ρ) s x =
      (fun o => match o with | none => weight P s x none | some z => primeOnly y ρ z * weight P s x (some z)) := by
    funext o; cases o <;> rfl
  rw [hw]; exact strengthIn_primed _ _ _ _

/-- **The chance of retrieving a primed code**: `ρ W_y / (ρ W_y + W_rest)`,
where `W_y` is the unprimed weight on `y` and `W_rest` that on every other
outcome, failure included. -/
theorem prob_primed (P : ActParams) (s : ActState) (x y : Item) (ρ : Rat) :
    prob (retrieveIn P (primeOnly y ρ) s x) (· == some y) =
      ρ * strengthIn (outcomes s) (weight P s x) (· == some y) /
        (ρ * strengthIn (outcomes s) (weight P s x) (· == some y) +
          strengthIn (outcomes s) (weight P s x) (fun o => !(o == some y))) := by
  have hw : weightIn P (primeOnly y ρ) s x =
      (fun o => match o with | none => weight P s x none | some z => primeOnly y ρ z * weight P s x (some z)) := by
    funext o; cases o <;> rfl
  obtain ⟨h1, h2⟩ := strengthIn_primed (outcomes s) (weight P s x) y ρ
  rw [retrieveIn, prob_sample, total, strengthIn_split _ _ (fun _ => true) (· == some y), hw]
  simp only [Bool.true_and] at *
  rw [h1, h2]
/-! ### What primes: seeing an item just before the test

In ACT-R, a recent use of a chunk raises its base level. Seeing `y` `j`
times just before the test, without advancing the clock, adds `j` to each of
`y`'s chunks' `e^B`, which multiplies `y`'s weight, for every probe, by one
factor: so recency is priming, with the factor derived (`retrieve_rehearse`). -/

/-- **Rehearsal**: `j` more uses of `y`, one step before now, without
advancing the clock: `y` seen `j` times just before the test. -/
def rehearse (s : ActState) (y : Item) (j : Nat) : ActState :=
  ⟨s.now, s.chunks.map fun c => if c.code = y then ⟨c.code, List.replicate j (s.now - 1) ++ c.uses⟩ else c⟩

/-- The total base level of the chunks with code `y`. -/
def baseOf (s : ActState) (y : Item) : Rat :=
  ((s.chunks.filter fun c => c.code == y).map fun c => baseWeight s.now c.uses).sum

/-- The number of chunks with code `y`. -/
def countOf (s : ActState) (y : Item) : Nat := (s.chunks.filter fun c => c.code == y).length

theorem sum_replicate_rat (j : Nat) (a : Rat) : (List.replicate j a).sum = (j : Rat) * a := by
  induction j with
  | zero => simp
  | succ j ih => simp [List.replicate_succ, ih]; grind

theorem baseWeight_rehearsed (now : Time) (j : Nat) (uses : List Time) (h : 1 ≤ now) :
    baseWeight now (List.replicate j (now - 1) ++ uses) = (j : Rat) + baseWeight now uses := by
  simp only [baseWeight, List.map_append, List.sum_append, List.map_replicate, sum_replicate_rat]
  have : now - (now - 1) = 1 := by unfold Time at *; omega
  rw [this]
  grind

theorem outcomes_rehearse (s : ActState) (y : Item) (j : Nat) :
    outcomes (rehearse s y j) = outcomes s := by
  simp only [outcomes, rehearse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp]
  split <;> rfl

/-- The weight on `y`, by chunk: base level times the mismatch factor, which
depends only on the code. -/
theorem weight_some_eq (P : ActParams) (s : ActState) (x y : Item) :
    weight P s x (some y) = baseOf s y * P.mu ^ mismatches P.fs x y := by
  simp only [weight, baseOf]
  generalize s.chunks = cs
  induction cs with
  | nil => simp
  | cons c cs ih =>
    by_cases h : c.code = y
    · simp [h, chunkWeight, ih]
      grind
    · have : (c.code == y) = false := by simp [h]
      simp [this, ih]

/-- Rehearsal of `y`, chunk by chunk. -/
abbrev reh (now : Time) (y : Item) (j : Nat) (c : Chunk) : Chunk :=
  if c.code = y then ⟨c.code, List.replicate j (now - 1) ++ c.uses⟩ else c

theorem reh_code (now : Time) (y : Item) (j : Nat) (c : Chunk) : (reh now y j c).code = c.code := by
  unfold reh; split <;> rfl

theorem filter_map_reh (now : Time) (y z : Item) (j : Nat) (cs : List Chunk) :
    (cs.map (reh now y j)).filter (fun c => c.code == z) =
      (cs.filter (fun c => c.code == z)).map (reh now y j) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro c _
  simp [reh_code]

theorem baseOf_rehearse_other (s : ActState) (y z : Item) (j : Nat) (hz : z ≠ y) :
    baseOf (rehearse s y j) z = baseOf s z := by
  simp only [baseOf, rehearse]
  rw [show (fun c => if c.code = y then (⟨c.code, List.replicate j (s.now - 1) ++ c.uses⟩ : Chunk) else c)
    = reh s.now y j from rfl, filter_map_reh, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  have : c.code = z := by simpa using (List.mem_filter.mp hc).2
  have : ¬ c.code = y := fun e => hz (this ▸ e)
  simp [reh, this]

theorem baseOf_rehearse_self (s : ActState) (y : Item) (j : Nat) (h : 1 ≤ s.now) :
    baseOf (rehearse s y j) y = baseOf s y + (countOf s y : Rat) * j := by
  simp only [baseOf, countOf, rehearse]
  rw [show (fun c => if c.code = y then (⟨c.code, List.replicate j (s.now - 1) ++ c.uses⟩ : Chunk) else c)
    = reh s.now y j from rfl, filter_map_reh, List.map_map]
  have hall : ∀ c ∈ s.chunks.filter (fun c => c.code == y), c.code = y := fun c hc => by
    simpa using (List.mem_filter.mp hc).2
  generalize s.chunks.filter (fun c => c.code == y) = L at hall ⊢
  induction L with
  | nil => simp; grind
  | cons c L ih =>
    have hc := hall c (List.mem_cons_self ..)
    have := ih (fun d hd => hall d (List.mem_cons_of_mem c hd))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp, reh, hc, ite_true] at this ⊢
    rw [baseWeight_rehearsed _ _ _ h, this]
    push_cast
    grind

/-- **Seeing `y` just before the test is priming `y`.** With the clock at 1
or later, `j` uses of `y` one step before now multiply `y`'s weight, for
every probe, by `ρ = 1 + k j / B`, where `B` is `y`'s base level and `k` the
number of its chunks, and leave every other weight alone. -/
theorem retrieve_rehearse (P : ActParams) (s : ActState) (y : Item) (j : Nat) (h : 1 ≤ s.now)
    (hB : baseOf s y ≠ 0) (x : Item) :
    retrieve P (rehearse s y j) x =
      retrieveIn P (primeOnly y (1 + (countOf s y : Rat) * j / baseOf s y)) s x := by
  simp only [retrieve, retrieveIn, outcomes_rehearse]
  congr 1
  funext o
  cases o with
  | none => rfl
  | some z =>
    simp only [weightIn, primeOnly]
    rw [weight_some_eq, weight_some_eq]
    by_cases hz : z = y
    · subst hz
      rw [baseOf_rehearse_self s z j h]
      simp only [ite_true]
      grind
    · rw [baseOf_rehearse_other s y z j hz]
      simp [hz]

end Act

/-- Declarative memory with activation, as a retriever. -/
def actRetriever (P : ActParams) : Retriever ActState Item := ⟨Act.study, Act.retrieve P⟩

/-- Stable retrieval holds vacuously: no chunk is ever retrieved for certain. -/
theorem actRetriever_stableRetrieval (P : ActParams) :
    Phenomena.StableRetrieval (actRetriever P) :=
  Laws.stableRetrieval_of_neverCertain _ (Act.retrieve_not_certain P)

end Cog
