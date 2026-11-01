/-
Processes: splitting a type (differentiation), and aiming a view at a type.

View application re-interprets operation *types* (`Process/ViewApplication`):
every instance of a matched type changes together. So two actions of one
type cannot be given different meanings by any view on that type
(`same_parent_same_reading`). Accounts of conceptual change call the
remedy *differentiation*: one concept becomes two. Here:

* `splitType T inst newT`: a new type frame `newT`, a copy of `inst`'s type
  (same kind, same slots), and `inst` re-parented to it.
* `retarget V old new`: rename the view's frame so that view application
  matches it, by identity, to the type frame `new`.

Main results, for any theory:
* `split_conservative`: a split changes no prediction, for any denotation
  that reads an action's type only through its slots (`ParentReader`). It
  only makes a later, separate re-interpretation possible.
* `split_separates`: afterwards, `inst` and the other instances of its old
  type have different types.
* `same_parent_same_reading`: two actions with the same type are read
  alike by such a denotation; with `predictT_head_congr`, sequences that
  differ only in which of them comes first are predicted alike.
-/

import CogLib.Process.TheoryExecution

namespace Cog

variable {A L S : Type} [DecidableEq A] [DecidableEq L]

/-- Rename one atom throughout a term. -/
def renameAtom (old new : A) (t : Term A) : Term A := t.rename fun a => if a = old then new else a

/-- **Aim a view at a type**: rename its frame `old` to `new`. -/
def retarget (V : KNet A L) (old new : A) : KNet A L :=
  ⟨V.links.map fun e => (renameAtom old new e.1, e.2.1, renameAtom old new e.2.2), V.isa⟩

/-- Re-parent `inst` to `newT`. -/
def reparentLink (isaL : L) (inst newT : A) (e : Term A × L × Term A) : Term A × L × Term A :=
  if e.1 = .atom inst ∧ e.2.1 = isaL then (e.1, e.2.1, .atom newT) else e

/-- **Split a type**: copy `inst`'s type frame as `newT`, and re-parent `inst`
to it. -/
def splitType (T : KNet A L) (inst newT : A) : KNet A L :=
  match T.parent inst with
  | none => T
  | some p => ⟨T.links.map (reparentLink T.isa inst newT) ++
      (T.links.filter fun e => e.1 = .atom p).map fun e => (.atom newT, e.2.1, e.2.2), T.isa⟩

/-- `n` does not occur in the theory, as a source or a value of any link. -/
def Fresh (T : KNet A L) (n : A) : Prop := ∀ e ∈ T.links, e.1 ≠ .atom n ∧ e.2.2 ≠ .atom n

/-- A denotation that reads the theory only through the slots of the acting
frame's type. -/
def ParentReader (den : KNet A L → A → Term A → S → Option S) : Prop :=
  ∃ d : (L → Option (Term A)) → Term A → S → Option S, ∀ T k f s,
    den T k f s = d (fun l => (T.parent k).bind fun p => T.slot p l) f s

section lemmas

variable (T : KNet A L) (inst newT p : A)

theorem targets_split_other (hp : T.parent inst = some p) (hf : Fresh T newT) (n : Term A) (l : L)
    (hn : n ≠ .atom newT) (hil : ¬ (n = .atom inst ∧ l = T.isa)) :
    (splitType T inst newT).targets n l = T.targets n l := by
  simp only [splitType, hp, SemNet.targets, List.filter_append, List.map_append]
  have h2 : ((T.links.filter fun e => e.1 = .atom p).map
      fun e => ((Term.atom newT : Term A), e.2.1, e.2.2)).filter
      (fun e => e.1 == n && e.2.1 == l) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    simp [Ne.symm hn]
  rw [h2, List.map_nil, List.append_nil, List.filter_map, List.map_map]
  have hP : ∀ e, (fun e : Term A × L × Term A => e.1 == n && e.2.1 == l) (reparentLink T.isa inst newT e) =
      (e.1 == n && e.2.1 == l) := by
    intro e; simp only [reparentLink]; split <;> rfl
  rw [show ((fun e : Term A × L × Term A => e.1 == n && e.2.1 == l) ∘ reparentLink T.isa inst newT) =
      (fun e => e.1 == n && e.2.1 == l) from funext hP]
  apply List.map_congr_left
  intro e he
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at he
  simp only [Function.comp, reparentLink]
  split
  · rename_i h; exact absurd ⟨he.2.1 ▸ h.1, he.2.2 ▸ h.2⟩ hil
  · rfl

theorem isa_split : (splitType T inst newT).isa = T.isa := by
  unfold splitType; split <;> rfl

theorem targets_split_new (hp : T.parent inst = some p) (hf : Fresh T newT) (l : L) :
    (splitType T inst newT).targets (.atom newT) l = T.targets (.atom p) l := by
  simp only [splitType, hp, SemNet.targets, List.filter_append, List.map_append]
  have h1 : (T.links.map (reparentLink T.isa inst newT)).filter
      (fun e => e.1 == .atom newT && e.2.1 == l) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    have := (hf e' he').1
    simp only [reparentLink]
    split <;> simp [this]
  rw [h1, List.map_nil, List.nil_append, List.filter_map, List.map_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro e _
  simp only [Function.comp, beq_self_eq_true, Bool.true_and]
  by_cases h : e.1 = .atom p <;> simp [h, Bool.and_comm]

theorem targets_split_inst (hp : T.parent inst = some p) (hf : Fresh T newT) :
    (splitType T inst newT).targets (.atom inst) T.isa =
      (T.targets (.atom inst) T.isa).map fun _ => .atom newT := by
  have hne : (Term.atom inst : Term A) ≠ .atom newT := by
    intro h
    cases h
    simp only [SemNet.parent, SemNet.slot, SemNet.targets] at hp
    cases hl : (T.links.filter fun e => e.1 == Term.atom inst && e.2.1 == T.isa) with
    | nil => simp [hl] at hp
    | cons e _ =>
      have he : e ∈ T.links.filter fun e => e.1 == Term.atom inst && e.2.1 == T.isa := by
        rw [hl]; exact List.mem_cons_self ..
      simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at he
      exact (hf e he.1).1 he.2.1
  simp only [splitType, hp, SemNet.targets, List.filter_append, List.map_append]
  have h2 : ((T.links.filter fun e => e.1 = .atom p).map
      fun e => ((Term.atom newT : Term A), e.2.1, e.2.2)).filter
      (fun e => e.1 == .atom inst && e.2.1 == T.isa) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    simp [Ne.symm hne]
  rw [h2, List.map_nil, List.append_nil, List.filter_map, List.map_map]
  have hP : ∀ e, (fun e : Term A × L × Term A => e.1 == .atom inst && e.2.1 == T.isa)
      (reparentLink T.isa inst newT e) = (e.1 == .atom inst && e.2.1 == T.isa) := by
    intro e; simp only [reparentLink]; split <;> rfl
  rw [show ((fun e : Term A × L × Term A => e.1 == .atom inst && e.2.1 == T.isa) ∘
      reparentLink T.isa inst newT) = (fun e => e.1 == .atom inst && e.2.1 == T.isa) from funext hP,
    List.map_map]
  apply List.map_congr_left
  intro e he
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at he
  simp [Function.comp, reparentLink, he.2.1, he.2.2]

/-- After a split, `inst`'s type is `newT`. -/
theorem parent_split_inst (hp : T.parent inst = some p) (hf : Fresh T newT) :
    (splitType T inst newT).parent inst = some newT := by
  have hne : (T.targets (.atom inst) T.isa) ≠ [] := by
    intro h; simp [SemNet.parent, SemNet.slot, h] at hp
  simp only [SemNet.parent, SemNet.slot, isa_split, targets_split_inst T inst newT p hp hf]
  cases h : T.targets (.atom inst) T.isa with
  | nil => exact absurd h hne
  | cons _ _ => rfl

/-- After a split, `newT` has the slots of `inst`'s old type. -/
theorem slot_split_new (hp : T.parent inst = some p) (hf : Fresh T newT) (l : L) :
    (splitType T inst newT).slot newT l = T.slot p l := by
  simp only [SemNet.slot, targets_split_new T inst newT p hp hf]

/-- Every other frame keeps its slots. -/
theorem slot_split_other (hp : T.parent inst = some p) (hf : Fresh T newT) (k : A) (l : L)
    (hk : k ≠ newT) (hil : ¬ (k = inst ∧ l = T.isa)) :
    (splitType T inst newT).slot k l = T.slot k l := by
  simp only [SemNet.slot]
  rw [targets_split_other T inst newT p hp hf _ l (by simpa using hk) (by simpa using hil)]

/-- Every other frame keeps its type. -/
theorem parent_split_other (hp : T.parent inst = some p) (hf : Fresh T newT) (k : A)
    (hk : k ≠ newT) (hki : k ≠ inst) : (splitType T inst newT).parent k = T.parent k := by
  simp only [SemNet.parent, isa_split]
  rw [slot_split_other T inst newT p hp hf k T.isa hk (fun h => hki h.1)]

/-- A frame's type occurs as the value of one of its links. -/
theorem mem_of_parent (k q : A) (h : T.parent k = some q) : ∃ e ∈ T.links, e.2.2 = .atom q := by
  simp only [SemNet.parent, SemNet.slot, SemNet.targets] at h
  cases hl : (T.links.filter fun e => e.1 == Term.atom k && e.2.1 == T.isa) with
  | nil => simp [hl] at h
  | cons e es =>
    rw [hl] at h
    simp only [List.map_cons, List.head?_cons] at h
    have he : e ∈ T.links.filter fun e => e.1 == Term.atom k && e.2.1 == T.isa := by
      rw [hl]; exact List.mem_cons_self ..
    refine ⟨e, (List.mem_filter.mp he).1, ?_⟩
    split at h
    · rename_i x hx; cases h; exact Option.some.inj hx
    · cases h

end lemmas

/-- **A split changes no prediction.** For a denotation that reads an
action's type only through its slots, and actions that are not `newT` and
not instances of `inst`, every prediction is the same after splitting
`inst`'s type. (`inst` now reads the copy, which has the same slots.) -/
theorem split_conservative (fnL : L) (den : KNet A L → A → Term A → S → Option S)
    (hd : ParentReader den) (T : KNet A L) (inst newT p : A) (hp : T.parent inst = some p)
    (hf : Fresh T newT) (hfn : fnL ≠ T.isa) (acts : List A)
    (hacts : ∀ k ∈ acts, k ≠ newT ∧ T.parent k ≠ some inst) (s : S) :
    predictT fnL den (splitType T inst newT) acts s = predictT fnL den T acts s := by
  obtain ⟨d, hd⟩ := hd
  apply predictT_congr
  intro k hk
  obtain ⟨hkn, hki⟩ := hacts k hk
  refine ⟨slot_split_other T inst newT p hp hf k fnL hkn (fun h => hfn h.2), fun f s => ?_⟩
  rw [hd, hd]
  congr 1
  funext l
  by_cases hkI : k = inst
  · subst hkI
    rw [parent_split_inst T k newT p hp hf, hp]
    simp only [Option.bind_some]
    exact slot_split_new T k newT p hp hf l
  · rw [parent_split_other T inst newT p hp hf k hkn hkI]
    cases hq : T.parent k with
    | none => rfl
    | some q =>
      simp only [Option.bind_some]
      have hqn : q ≠ newT := by
        intro h; subst h
        obtain ⟨e, he, hv⟩ := mem_of_parent T k q hq
        exact (hf e he).2 hv
      have hqi : q ≠ inst := fun h => hki (h ▸ hq)
      exact slot_split_other T inst newT p hp hf q l hqn (fun h => hqi h.1)

/-- **A split separates**: afterwards `inst` and another instance `k` of its
old type have different types. -/
theorem split_separates (T : KNet A L) (inst newT p k : A) (hp : T.parent inst = some p)
    (hf : Fresh T newT) (hk : T.parent k = some p) (hki : k ≠ inst) (hkn : k ≠ newT) :
    (splitType T inst newT).parent inst ≠ (splitType T inst newT).parent k := by
  rw [parent_split_inst T inst newT p hp hf, parent_split_other T inst newT p hp hf k hkn hki, hk]
  intro h
  cases h
  obtain ⟨e, he, hv⟩ := mem_of_parent T inst newT hp
  exact (hf e he).2 hv

/-- **Actions of one type are read alike.** -/
theorem same_parent_same_reading (den : KNet A L → A → Term A → S → Option S)
    (hd : ParentReader den) (T : KNet A L) (k₁ k₂ : A) (h : T.parent k₁ = T.parent k₂)
    (f : Term A) (s : S) : den T k₁ f s = den T k₂ f s := by
  obtain ⟨d, hd⟩ := hd
  rw [hd, hd, h]

/-- Sequences that differ only in their first action are predicted alike if
the two first actions are read alike. -/
theorem predictT_head_congr (fnL : L) (den : KNet A L → A → Term A → S → Option S) (T : KNet A L)
    (k₁ k₂ : A) (f₁ f₂ : Term A) (rest : List A) (s : S)
    (h₁ : T.slot k₁ fnL = some f₁) (h₂ : T.slot k₂ fnL = some f₂)
    (hden : den T k₁ f₁ s = den T k₂ f₂ s) :
    predictT fnL den T (k₁ :: rest) s = predictT fnL den T (k₂ :: rest) s := by
  simp only [predictT, h₁, h₂, hden]

end Cog
