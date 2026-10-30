/-
Processes: selective modification of a prototype (Smith, Osherson, Rips &
Keane 1988).

An adjective naming one value of one attribute (`red`: color) modifies a
noun's prototype (`apple`). It selects that attribute, shifts all of its
votes to the named value, and multiplies its diagnosticity by a boost (2 in
the paper, "an arbitrary choice"). Every other attribute is unchanged.
-/

import CogLib.Rep.Frames

namespace Cog

variable {A V : Type} [DecidableEq A] [DecidableEq V]

/-- **Selective modification** of `P` by the value `v0` of attribute `i0`. -/
def modify (S : Schema A V) (boost : Rat) (i0 : A) (v0 : V) (P : Proto A V) : Proto A V where
  diag i := if i = i0 then boost * P.diag i else P.diag i
  votes i v := if i = i0 then (if v = v0 then votesOn (S.vals i0) (P.votes i0) else 0)
    else P.votes i v

/-- A sum over a list without repeats changes only by the change at `i0`,
when that is the only place the summands differ. -/
theorem sum_map_update (as : List A) (hnd : as.Nodup) (i0 : A) (hi : i0 ∈ as) (f g : A → Rat)
    (h : ∀ i, i ≠ i0 → f i = g i) :
    (as.map f).sum = (as.map g).sum + (f i0 - g i0) := by
  induction as with
  | nil => simp at hi
  | cons j as ih =>
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hj : j = i0
    · subst hj
      have hrest : (as.map f).sum = (as.map g).sum := by
        congr 1
        apply List.map_congr_left
        intro i hi'
        exact h i (fun e => hnd'.1 (e ▸ hi'))
      rw [hrest]; grind
    · have hi' : i0 ∈ as := by
        rcases List.mem_cons.mp hi with e | e
        · exact absurd e.symm hj
        · exact e
      rw [ih hnd'.2 hi', h j hj]; grind

/-- Modification changes similarity only on the selected attribute. -/
theorem sim_modify (K : Contrast) (S : Schema A V) (hnd : S.attrs.Nodup) (boost : Rat) (i0 : A)
    (hi : i0 ∈ S.attrs) (v0 : V) (P : Proto A V) (I : Inst A V) :
    sim K S (modify S boost i0 v0 P) I = sim K S P I +
      (boost * P.diag i0 * attrContrast K (S.vals i0) (fun v => if v = v0 then
          votesOn (S.vals i0) (P.votes i0) else 0) (I i0) -
        P.diag i0 * attrContrast K (S.vals i0) (P.votes i0) (I i0)) := by
  unfold sim
  rw [sum_map_update S.attrs hnd i0 hi _
    (fun i => P.diag i * attrContrast K (S.vals i) (P.votes i) (I i))
    (fun i hne => by simp only [modify, hne, ite_false])]
  simp only [modify, ite_true]

end Cog
