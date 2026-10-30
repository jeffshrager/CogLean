/-
Processes: categorization by concepts held in a knowledge net.

A concept is a frame. Its prototype is in the net: votes are links
`(c, voteL, av [attr, value, n])`, diagnosticities `(c, diagL, dv [attr, n])`
(`protoOfNet`). How membership is decided, and how two concepts combine, are
slots of the concept's *type* frame, so a view can replace them (view
application, `Process/ViewApplication`):

* `test`: `simTest []` decides membership by similarity to the prototype,
  graded by the threshold model (Hampton 2007); any other test is a rule,
  given meaning by the domain (`rule`), with its holes filled from the
  concept's `named` slot through the type frame's `named` pattern;
* `combine`: `modifyComb []` combines an adjective with a noun by selective
  modification of the noun's prototype (Smith et al. 1988), then tests
  similarity; `conjComb []` takes the lesser of the two memberships.

Typicality is always similarity to the prototype (or to the modified
prototype, for a combination): it reads only the concept's own links.

Main result: two nets that agree on a concept's prototype links give it the
same typicality, for every instance (`typicality_congr`), so a change that
leaves those links alone, such as a view replacing the type frame's test,
leaves typicality as it was.
-/

import CogLib.Rep.Frames
import CogLib.Process.Combination
import CogLib.Process.ViewApplication
import CogLib.Phenomena.Combination

namespace Cog

variable {A L I : Type} [DecidableEq A] [DecidableEq L]

/-- The labels and functors of categorization, and the domain's parts. -/
structure CatConfig (A L I : Type) where
  voteL : L
  diagL : L
  testL : L
  combineL : L
  namedL : L
  adjL : L
  av : A
  dv : A
  simTest : A
  modifyComb : A
  num : A → Rat
  K : Contrast
  boost : Rat
  SL : Rat
  SH : Rat
  S : Schema A A
  inst : I → Inst A A
  rule : Term A → I → Bool

/-- The weight in the first link `(c, l, f [args..., n])` whose arguments
before the count match. -/
def weightOf (C : CatConfig A L I) (G : KNet A L) (c : A) (l : L) (f : A) (args : List A) : Rat :=
  match (G.targets (.atom c) l).find? fun t => match t with
      | .app g ts => g == f && ts.take args.length == args.map .atom
      | _ => false with
  | some (.app _ ts) => match ts.drop args.length with
    | [.atom n] => C.num n
    | _ => 0
  | _ => 0

/-- **A prototype read from the net.** -/
def protoOfNet (C : CatConfig A L I) (G : KNet A L) (c : A) : Proto A A where
  diag i := weightOf C G c C.diagL C.dv [i]
  votes i v := weightOf C G c C.voteL C.av [i, v]

/-- Typicality of an instance in concept `c`. -/
def typicality (C : CatConfig A L I) (G : KNet A L) (c : A) (x : I) : Rat :=
  sim C.K C.S (protoOfNet C G c) (C.inst x)

/-- The adjective's attribute and value: `(adj, adjL, av [attr, value])`. -/
def adjOf (G : KNet A L) (C : CatConfig A L I) (adj : A) : Option (A × A) :=
  match (G.targets (.atom adj) C.adjL).head? with
  | some (.app _ [.atom i, .atom v]) => some (i, v)
  | _ => none

/-- Typicality of an instance in the combination *adj noun*: similarity to
the noun's prototype modified by the adjective. -/
def typicality2 (C : CatConfig A L I) (G : KNet A L) (adj noun : A) (x : I) : Rat :=
  match adjOf G C adj with
  | some (i, v) => sim C.K C.S (modify C.S C.boost i v (protoOfNet C G noun)) (C.inst x)
  | none => typicality C G noun x

/-- A slot inherited from the concept's type frame. -/
def typeSlot (G : KNet A L) (c : A) (l : L) : Option (Term A) :=
  (G.parent c).bind fun p => G.slot p l

/-- **Membership** of an instance in concept `c`, in [0, 1]. -/
def membership (C : CatConfig A L I) (G : KNet A L) (c : A) (x : I) : Rat :=
  match typeSlot G c C.testL with
  | some test =>
    if test = .app C.simTest [] then thresholdM C.SL C.SH (typicality C G c x)
    else
      let σ := match typeSlot G c C.namedL, G.slot c C.namedL with
        | some pat, some name => (pat.unify name).getD []
        | _, _ => []
      if C.rule (test.fill σ) x then 1 else 0
  | none => 0

/-- **Membership in a combination** *adj noun*, by the noun's type frame's
`combine` slot. -/
def membership2 (C : CatConfig A L I) (G : KNet A L) (adj noun : A) (x : I) : Rat :=
  if typeSlot G noun C.combineL = some (.app C.modifyComb []) then
    thresholdM C.SL C.SH (typicality2 C G adj noun x)
  else min (membership C G adj x) (membership C G noun x)

theorem weightOf_congr (C : CatConfig A L I) (G G' : KNet A L) (c : A) (l : L) (f : A)
    (args : List A) (h : G.targets (.atom c) l = G'.targets (.atom c) l) :
    weightOf C G c l f args = weightOf C G' c l f args := by
  simp only [weightOf, h]

/-- **Typicality depends only on the concept's prototype links.** -/
theorem typicality_congr (C : CatConfig A L I) (G G' : KNet A L) (c : A)
    (hv : G.targets (.atom c) C.voteL = G'.targets (.atom c) C.voteL)
    (hd : G.targets (.atom c) C.diagL = G'.targets (.atom c) C.diagL) (x : I) :
    typicality C G c x = typicality C G' c x := by
  have : protoOfNet C G c = protoOfNet C G' c := by
    simp only [protoOfNet, weightOf_congr C G G' c C.diagL C.dv _ hd,
      weightOf_congr C G G' c C.voteL C.av _ hv]
  simp only [typicality, this]

end Cog
