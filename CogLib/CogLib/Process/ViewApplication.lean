/-
Processes: view application (Shrager 1987, §3.4.2), on knowledge nets.

A knowledge net is a semantic net whose nodes are terms (`Rep/Terms`). A
*frame* is an atom with links. A *type* frame has a kind (a link labelled
`kindL`: operation type, object type, script) and no parent; an *instance*
frame has a parent (an `isa` link to an atom). Slot values are terms;
patterns (terms with holes) in type frames say what their instances' slots
hold ("Set the program-plan to a Real-World-Action"). Applying a view to a
theory:

1. copies the view (the *base*);
2. merges the theory into it. Each theory type frame is matched to the
   view's frame of the same abstract type (the same atom), or else to a
   view type frame of the same kind, chosen at random among those not yet
   used, or left unmatched. Where both say something about a slot of a
   matched frame, the view wins; everything else in the theory is copied,
   with matched frames renamed throughout, so an instance of a matched type
   becomes an instance of the view's type;
3. coerces each slot of a re-parented instance: its value is matched
   against the old parent's pattern for the slot, and the new parent's
   pattern is filled with the result;
4. fills the holes in the view's instance frames: a hole of type `τ` is
   filled by a theory atom linked to `τ` by `fillL` (a button whose label
   indicates the view);
5. makes each object play a role in one operation only: an atom bound in
   step 4 is removed from every other frame's lists, and a script that ran
   the operation which lost it now also runs, next, the operation which
   gained it.

Ambiguity is resolved at random and never revisited (p. 261), so
application gives a distribution over theories.

Main results, for any view, theory and matching: the view is kept whole
(`merge_keeps_view`); on a matched frame the view's slots win
(`merge_view_wins`: non-monotonic change); every unmatched theory frame
keeps its links, renamed (`merge_keeps_unmatched`), and an instance of a
matched type becomes an instance of the view's type (`merge_reparents`).
-/

import CogLib.Rep.SemanticNet
import CogLib.Rep.Terms
import CogLib.Rep.Distribution

namespace Cog

variable {A L : Type} [DecidableEq A] [DecidableEq L]

/-- A knowledge net: a semantic net over terms. -/
abbrev KNet (A L : Type) := SemNet (Term A) L

/-- The labels view application uses. -/
structure VAConfig (L : Type) where
  kindL : L
  fillL : L

namespace SemNet

/-- The atoms that are frames (have outgoing links), each once. -/
def frames (G : KNet A L) : List A :=
  (G.links.filterMap fun e => match e.1 with
    | .atom a => some a
    | _ => none).eraseDups

/-- The first value of slot `l` of frame `f`. -/
def slot (G : KNet A L) (f : A) (l : L) : Option (Term A) := (G.targets (.atom f) l).head?

/-- The parent of a frame. -/
def parent (G : KNet A L) (f : A) : Option A :=
  match G.slot f G.isa with
  | some (.atom p) => some p
  | _ => none

/-- Type frames: frames with a kind and no parent. -/
def typeFrames (G : KNet A L) (kindL : L) : List A :=
  G.frames.filter fun f => G.targets (.atom f) kindL != [] && G.targets (.atom f) G.isa == []

end SemNet

/-- A matching: theory type frames to view type frames. -/
abbrev Matching (A : Type) := List (A × A)

/-- Rename matched frames throughout a term. -/
def rn (m : Matching A) (t : Term A) : Term A := t.rename fun a => (m.lookup a).getD a

/-- A uniform choice. -/
def uniform {α : Type} (xs : List α) : Dist α := xs.map fun x => (x, 1 / (xs.length : Rat))

/-- Step 2's matchings: each theory type frame in turn, to the view's frame of
the same abstract type if there is one, else to an unused view type frame
of the same kind, chosen uniformly; unmatched if there is none. -/
def matchings (V T : KNet A L) (kindL : L) : List A → Matching A → Dist (Matching A)
  | [], used => Dist.pure used
  | t :: ts, used =>
    let cands := (V.typeFrames kindL).filter fun v =>
      V.slot v kindL == T.slot t kindL && !(used.any fun p => p.2 == v)
    if cands.contains t then matchings V T kindL ts ((t, t) :: used)
    else if cands = [] then matchings V T kindL ts used
    else Dist.bind (uniform cands) fun v => matchings V T kindL ts ((t, v) :: used)

/-- Whether a theory link survives step 2: not if its frame is matched and
the view says something about the same slot. -/
def survives (V : KNet A L) (m : Matching A) (e : Term A × L × Term A) : Bool :=
  match e.1 with
  | .atom a => match m.lookup a with
    | some b => V.targets (.atom b) e.2.1 == []
    | none => true
  | _ => true

/-- Steps 1–2: the view, plus the theory's surviving links, renamed. -/
def merge (V T : KNet A L) (m : Matching A) : KNet A L where
  isa := V.isa
  links := V.links ++ ((T.links.filter (survives V m)).map fun e => (rn m e.1, e.2.1, rn m e.2.2))

/-- Step 3: coerce each slot of a re-parented instance, from its old parent's
pattern to its new parent's. -/
def coerce (T : KNet A L) (m : Matching A) (G : KNet A L) : KNet A L :=
  { G with links := G.links.map fun e =>
      match e.1 with
      | .atom i => match T.parent i with
        | some p => match m.lookup p, T.slot p e.2.1 with
          | some q, some op => match op.unify e.2.2, G.slot q e.2.1 with
            | some σ, some np => if np.hasHole then (e.1, e.2.1, np.fill σ) else e
            | _, _ => e
          | _, _ => e
        | none => e
      | _ => e }

/-- The theory atom that fills a hole of type `τ`. -/
def filler (K : VAConfig L) (T : KNet A L) (τ : A) : Option (Term A) :=
  (T.links.find? fun e => e.2.1 == K.fillL && e.2.2 == .atom τ).map (·.1)

/-- The bindings step 4 makes for a pattern. -/
def holeSubst (K : VAConfig L) (T : KNet A L) : Term A → Term.Subst A
  | .app _ ps => ps.filterMap fun p => match p with
    | .hole τ => (filler K T τ).map fun x => (τ, x)
    | _ => none
  | .hole τ => ((filler K T τ).map fun x => [(τ, x)]).getD []
  | _ => []

/-- Whether a node is an instance frame. -/
def isInst (G : KNet A L) : Term A → Bool
  | .atom f => (G.parent f).isSome
  | _ => false

/-- Step 4: fill the holes of instance frames' slots. Also returns what was
bound, and to which frame. -/
def bindHoles (K : VAConfig L) (T : KNet A L) (G : KNet A L) : KNet A L × List (A × A) :=
  let bound := G.links.flatMap fun e =>
    if isInst G e.1 && e.2.2.hasHole then
      match e.1 with
      | .atom f => (holeSubst K T e.2.2).flatMap fun (_, x) => match x with
          | .atom a => [(f, a)]
          | _ => []
      | _ => []
    else []
  ({ G with links := G.links.map fun e =>
      if isInst G e.1 && e.2.2.hasHole then (e.1, e.2.1, e.2.2.fill (holeSubst K T e.2.2)) else e },
   bound)

/-- The type of the operation instance whose slots mention frame `g`. -/
def opTypeUsing (G : KNet A L) (g : A) : Option A :=
  (G.links.find? fun e => e.2.2.atoms.contains g && match e.1 with
      | .atom o => (G.parent o).isSome && o != g
      | _ => false).bind fun e => match e.1 with
    | .atom o => G.parent o
    | _ => none

/-- Insert `y` after every occurrence of `x` in a list of terms. -/
def insertAfter (x y : A) : List (Term A) → List (Term A)
  | [] => []
  | t :: ts => if t == .atom x then t :: .atom y :: insertAfter x y ts else t :: insertAfter x y ts

/-- Whether a node is a type frame. -/
def isType (K : VAConfig L) (G : KNet A L) (t : Term A) : Bool :=
  G.targets t K.kindL != [] && G.targets t G.isa == []

/-- Step 5: an atom bound to frame `f` leaves every other frame's lists; a
script running the operation that lost it then runs the one that gained it. -/
def singleFunction (K : VAConfig L) (G : KNet A L) (bound : List (A × A)) : KNet A L :=
  bound.foldl (fun G (f, a) =>
    let other (e : Term A × L × Term A) : Bool := e.1 != .atom f && e.2.1 != K.fillL
    let losers := G.links.filterMap fun e => match e.1 with
      | .atom g => if other e && e.2.2.atoms.contains a then some g else none
      | _ => none
    let edits := losers.filterMap fun g => match opTypeUsing G g, opTypeUsing G f with
      | some x, some y => some (x, y)
      | _, _ => none
    { G with links := G.links.map fun e =>
        let v := if other e then e.2.2.dropAtoms (· == a) else e.2.2
        match v with
        | .app h ts => if isType K G e.1 then
            (e.1, e.2.1, .app h (edits.foldl (fun ts (x, y) => insertAfter x y ts) ts))
          else (e.1, e.2.1, v)
        | _ => (e.1, e.2.1, v) }) G

/-- **View application**: a distribution over the resulting theories. -/
def applyView (K : VAConfig L) (V T : KNet A L) : Dist (KNet A L) :=
  Dist.bind (matchings V T K.kindL (T.typeFrames K.kindL) []) fun m =>
    let r := bindHoles K T (coerce T m (merge V T m))
    Dist.pure (singleFunction K r.1 r.2)

/-- The view is kept whole by the merge. -/
theorem merge_keeps_view (V T : KNet A L) (m : Matching A) (e : Term A × L × Term A)
    (he : e ∈ V.links) : e ∈ (merge V T m).links :=
  List.mem_append_left _ he

/-- Every link of an unmatched theory frame survives the merge, renamed. -/
theorem merge_keeps_unmatched (V T : KNet A L) (m : Matching A) (s : A) (t : Term A) (l : L)
    (hs : m.lookup s = none) (he : (.atom s, l, t) ∈ T.links) :
    (.atom s, l, rn m t) ∈ (merge V T m).links := by
  apply List.mem_append_right
  rw [List.mem_map]
  refine ⟨(.atom s, l, t), List.mem_filter.mpr ⟨he, by simp [survives, hs]⟩, ?_⟩
  simp [rn, Term.rename, hs]

/-- An instance of a matched type becomes an instance of the view's type. -/
theorem merge_reparents (V T : KNet A L) (m : Matching A) (i p q : A)
    (hi : m.lookup i = none) (hp : m.lookup p = some q) (he : (.atom i, T.isa, .atom p) ∈ T.links) :
    (.atom i, T.isa, .atom q) ∈ (merge V T m).links := by
  have := merge_keeps_unmatched V T m i (.atom p) T.isa hi he
  simpa [rn, Term.rename, hp] using this

/-- **On a matched frame the view wins**: where the view says something about
a slot of frame `v`, the merged net says exactly what the view says, provided
only matched theory frames are renamed to `v`. -/
theorem merge_view_wins (V T : KNet A L) (m : Matching A) (v : A) (l : L)
    (hv : V.targets (.atom v) l ≠ [])
    (honly : ∀ t : Term A, rn m t = .atom v → ∃ a, t = .atom a ∧ m.lookup a = some v) :
    (merge V T m).targets (.atom v) l = V.targets (.atom v) l := by
  have hnil : (((T.links.filter (survives V m)).map fun e => (rn m e.1, e.2.1, rn m e.2.2)).filter
      fun e => e.1 == .atom v && e.2.1 == l) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he hp
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    have hsurv := (List.mem_filter.mp he0).2
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    obtain ⟨a, ha, hb⟩ := honly e0.1 h1
    rw [survives, ha] at hsurv
    simp only [hb, beq_iff_eq] at hsurv
    rw [h2] at hsurv
    exact hv hsurv
  unfold SemNet.targets merge
  simp only [List.filter_append, hnil, List.append_nil]

end Cog
