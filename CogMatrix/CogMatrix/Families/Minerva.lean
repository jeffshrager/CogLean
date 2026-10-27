/-
A family of memories: global matching (MINERVA 2, Hintzman 1984).

Every study stores a separate trace. A probe activates every trace at once,
by the cube of its similarity to the probe, and memory returns the *echo*:
the activation-weighted sum of all traces, read feature by feature. The echo
need not be any stored trace. Probed with the centre of several studied
variants, it returns the centre, which was never studied (schema
abstraction).

Here features are binary (`±1`), every feature of a trace is stored
(encoding probability 1), and the echo is read as a code by the sign of each
feature. Retrieval fails when the echo's intensity (total activation) is not
positive.
-/

import CogLib

namespace Cog

/-- The parameter: the number of features compared, `0, …, width - 1`. -/
structure MinParams where
  width : Nat

/-- A memory state: the traces, in order of study. -/
abbrev MinState := List Item

namespace Minerva

/-- A feature as `±1`. -/
def val (b : Bool) : Rat := if b then 1 else -1

def features (P : MinParams) : List Feature := List.range P.width

/-- Similarity of probe and trace: the mean product of their features. -/
def sim (P : MinParams) (x t : Item) : Rat :=
  ((features P).map fun f => val (x.feat f) * val (t.feat f)).sum / P.width

/-- A trace's activation: the cube of its similarity. -/
def act (P : MinParams) (x t : Item) : Rat := sim P x t ^ 3

/-- The echo's intensity: the total activation. -/
def intensity (P : MinParams) (s : MinState) (x : Item) : Rat := (s.map (act P x)).sum

/-- The echo's content on feature `f`. -/
def content (P : MinParams) (s : MinState) (x : Item) (f : Feature) : Rat :=
  (s.map fun t => act P x t * val (t.feat f)).sum

/-- The echo, read as a code. -/
def echo (P : MinParams) (s : MinState) (x : Item) : Item :=
  (features P).map fun f => decide (0 < content P s x f)

/-- **Retrieval**: the echo, if its intensity is positive. -/
def retrieve (P : MinParams) (s : MinState) (x : Item) : Dist (Option Item) :=
  if 0 < intensity P s x then Dist.pure (some (echo P s x)) else Dist.pure none

/-- **Study** stores a new trace. -/
def study (s : MinState) (y : Item) : MinState := s ++ [y]

end Minerva

/-- Global matching as a retriever. -/
def minRetriever (P : MinParams) : Retriever MinState Item := ⟨Minerva.study, Minerva.retrieve P⟩

end Cog
