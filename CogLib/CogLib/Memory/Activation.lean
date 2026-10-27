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
-/

import CogLib.Rep.Distribution
import CogLib.Rep.Features
import CogLib.Phenomena.Retriever

namespace Cog

/-- A chunk: a stored code, and the times it was used. -/
structure Chunk where
  code : Item
  uses : List Nat
  deriving Repr, DecidableEq

/-- Declarative memory: the current time, and the chunks. -/
structure ActState where
  now : Nat
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
def baseWeight (now : Nat) (uses : List Nat) : Rat :=
  (uses.map fun t => 1 / ((now - t : Nat) : Rat)).sum

/-- `e^A` for a chunk's activation `A` given the probe `x`. -/
def chunkWeight (P : ActParams) (now : Nat) (x : Item) (c : Chunk) : Rat :=
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
def addUse (t : Nat) (x : Item) : List Chunk → List Chunk
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

end Act

/-- Declarative memory with activation, as a retriever. -/
def actRetriever (P : ActParams) : Retriever ActState Item := ⟨Act.study, Act.retrieve P⟩

/-- Stable retrieval holds vacuously: no chunk is ever retrieved for certain. -/
theorem actRetriever_stableRetrieval (P : ActParams) :
    Phenomena.StableRetrieval (actRetriever P) :=
  fun s _ y h _ => absurd h (Act.retrieve_not_certain P s y y)

end Cog
