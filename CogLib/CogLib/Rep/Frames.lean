/-
Representations: attribute–value frames (prototypes).

A prototype lists attributes (color, shape), each with a *diagnosticity*,
and for each attribute votes (salience) on its values (red 25, green 5).
An instance has votes too, but no diagnosticity. Similarity is Tversky's
contrast rule, applied attribute by attribute: each vote counts as a
feature, so `n` votes on red are `n` copies of red, and the features
common to the two, those distinct to the prototype and those distinct to
the instance are weighed by `a`, `b` and `c` and by the prototype's
diagnosticity (Smith, Osherson, Rips & Keane 1988, Eq. 2).
-/

namespace Cog

/-- A frame's vocabulary: its attributes, and each attribute's values. -/
structure Schema (A V : Type) where
  attrs : List A
  vals : A → List V

/-- A prototype: a diagnosticity for each attribute, and votes for each value. -/
structure Proto (A V : Type) where
  diag : A → Rat
  votes : A → V → Rat

/-- An instance: votes for each value of each attribute. -/
abbrev Inst (A V : Type) := A → V → Rat

/-- The weights of the contrast rule: common features, features distinct to
the prototype, features distinct to the instance. -/
structure Contrast where
  a : Rat
  b : Rat
  c : Rat

/-- The total votes on an attribute. -/
def votesOn {V : Type} (vs : List V) (p : V → Rat) : Rat := (vs.map p).sum

/-- The contrast on one attribute, before diagnosticity: on each value, the
votes common to prototype and instance count for, and the rest against. -/
def attrContrast {V : Type} (K : Contrast) (vs : List V) (p i : V → Rat) : Rat :=
  (vs.map fun v => K.a * min (p v) (i v) - K.b * (p v - min (p v) (i v)) -
    K.c * (i v - min (p v) (i v))).sum

/-- **Similarity** of an instance to a prototype: the contrast on each
attribute, weighted by the prototype's diagnosticity, summed. -/
def sim {A V : Type} (K : Contrast) (S : Schema A V) (P : Proto A V) (I : Inst A V) : Rat :=
  (S.attrs.map fun i => P.diag i * attrContrast K (S.vals i) (P.votes i) (I i)).sum

/-- An instance with all `n i` of its votes on attribute `i` on one value, `val i`. -/
def Inst.pure {A V : Type} [DecidableEq V] (val : A → V) (n : A → Rat) : Inst A V :=
  fun i v => if v = val i then n i else 0

theorem votesOn_nonneg {V : Type} (vs : List V) (p : V → Rat) (hp : ∀ v, 0 ≤ p v) :
    0 ≤ votesOn vs p := by
  induction vs with
  | nil => simp [votesOn]
  | cons v vs ih =>
    simp only [votesOn, List.map_cons, List.sum_cons] at ih ⊢
    have := hp v
    grind

theorem le_votesOn {V : Type} (vs : List V) (p : V → Rat) (hp : ∀ v, 0 ≤ p v) (w : V)
    (hw : w ∈ vs) : p w ≤ votesOn vs p := by
  induction vs with
  | nil => simp at hw
  | cons v vs ih =>
    simp only [votesOn, List.map_cons, List.sum_cons] at ih ⊢
    have h0 := votesOn_nonneg vs p hp
    simp only [votesOn] at h0
    rcases List.mem_cons.mp hw with h | h
    · subst h; grind
    · have := ih h; have := hp v; grind

/-- On an attribute where the instance has all `n` of its votes on `w`, the
contrast is `a·m − b·(T − m) − c·(n − m)`, where `T` is the prototype's
total and `m = min (p w) n` the votes they share. -/
theorem attrContrast_pure {V : Type} [DecidableEq V] (K : Contrast) (vs : List V) (p : V → Rat)
    (hp : ∀ v, 0 ≤ p v) (w : V) (n : Rat) (hvs : vs.Nodup) (hw : w ∈ vs) :
    attrContrast K vs p (fun v => if v = w then n else 0) =
      K.a * min (p w) n - K.b * (votesOn vs p - min (p w) n) - K.c * (n - min (p w) n) := by
  induction vs with
  | nil => simp at hw
  | cons v vs ih =>
    have hnd := List.nodup_cons.mp hvs
    simp only [attrContrast, votesOn, List.map_cons, List.sum_cons] at ih ⊢
    by_cases hv : v = w
    · subst hv
      -- every other value has no instance votes
      have hrest : ∀ us : List V, v ∉ us →
          (us.map fun u => K.a * min (p u) (if u = v then n else 0) -
            K.b * (p u - min (p u) (if u = v then n else 0)) -
            K.c * ((if u = v then n else 0) - min (p u) (if u = v then n else 0))).sum =
          -(K.b * (us.map p).sum) := by
        intro us hus
        induction us with
        | nil => simp
        | cons u us ih' =>
          have hu : u ≠ v := fun h => hus (h ▸ List.mem_cons_self)
          have hus' : v ∉ us := fun h => hus (List.mem_cons_of_mem _ h)
          simp only [List.map_cons, List.sum_cons, hu, ite_false, ih' hus']
          have : min (p u) 0 = 0 := by have := hp u; rw [Rat.min_def]; split <;> grind
          rw [this]
          grind
      simp only [ite_true, hrest vs hnd.1]
      grind
    · have hw' : w ∈ vs := by
        rcases List.mem_cons.mp hw with h | h
        · exact absurd h.symm hv
        · exact h
      simp only [hv, ite_false]
      rw [ih hnd.2 hw']
      have : min (p v) 0 = 0 := by have := hp v; rw [Rat.min_def]; split <;> grind
      rw [this]
      grind

/-- All the votes of a one-value attribute are on that value. -/
theorem votesOn_pure {V : Type} [DecidableEq V] (vs : List V) (w : V) (n : Rat) (hvs : vs.Nodup)
    (hw : w ∈ vs) : votesOn vs (fun v => if v = w then n else 0) = n := by
  induction vs with
  | nil => simp at hw
  | cons v vs ih =>
    have hnd := List.nodup_cons.mp hvs
    simp only [votesOn, List.map_cons, List.sum_cons] at ih ⊢
    by_cases hv : v = w
    · subst hv
      have : (vs.map fun u => if u = v then n else 0).sum = 0 := by
        have hz : ∀ us : List V, v ∉ us → (us.map fun u => if u = v then n else 0).sum = 0 := by
          intro us hus
          induction us with
          | nil => simp
          | cons u us ih' =>
            have hu : u ≠ v := fun h => hus (h ▸ List.mem_cons_self)
            simp only [List.map_cons, List.sum_cons, hu, ite_false,
              ih' (fun h => hus (List.mem_cons_of_mem _ h))]
            grind
        exact hz vs hnd.1
      simp only [ite_true, this]; grind
    · have hw' : w ∈ vs := by
        rcases List.mem_cons.mp hw with h | h
        · exact absurd h.symm hv
        · exact h
      simp only [hv, ite_false, ih hnd.2 hw']; grind

end Cog
