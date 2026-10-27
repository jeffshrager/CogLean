/-
The activation family (ACT-R's declarative memory, decay 1 and temperature 1)
against the laws.

Regime: from an empty memory, with a positive failure weight `θ` and a
positive discount `μ` per mismatch.

* `recency`: has it, for every such choice of parameters. Of two stimuli
  studied last, the later is retrieved more often (twice as often, in fact).
* `not_certainty`: lacks it. Retrieval can fail.
* `not_stability`: lacks it. Uses decay, and new chunks compete.
* `not_orderFree`: lacks it. The order of study sets the ages of the uses.
-/

import CogMatrix.Matrix.Common

namespace Cog.Matrix.Activation

open Laws Dist

/-- An empty memory. -/
def empty : ActState := ⟨0, []⟩

/-! ### Counterexamples -/

/-- All eight 3-bit codes compared, each mismatch halving the weight, failure
weight 1/10. -/
def P : ActParams := ⟨F3, 1 / 2, 1 / 10⟩

/-- **Activation lacks certainty**: 000, just studied, is retrieved by itself
with probability 10/11. -/
theorem not_certainty : ¬ Certainty (actRetriever P) empty U3 := by
  intro h
  have := h empty ⟨[], by decide, rfl⟩ (bits 0) (by decide)
  revert this
  decide +kernel

/-- **Activation lacks stability**: studying 100 after 000 changes the chance
that 000 retrieves itself. -/
theorem not_stability : ¬ Stability (actRetriever P) empty U3 := by
  intro h
  have := h ((actRetriever P).studyAll empty [bits 0]) ⟨_, by decide, rfl⟩ (bits 0) (by decide)
    (bits 1) (by decide) (by decide)
  revert this
  decide +kernel

/-- **Activation is not order-free**: 000 then 100 leaves memory retrieving
differently from 100 then 000. -/
theorem not_orderFree : ¬ OrderFree (actRetriever P) empty U3 := by
  intro h
  have := h empty ⟨[], by decide, rfl⟩ (bits 0) (by decide) (bits 1) (by decide) (bits 0)
  revert this
  decide +kernel

/-! ### Recency, in general -/

section Recency

variable (Q : ActParams)

def codes (s : ActState) : List Item := s.chunks.map Chunk.code

theorem addUse_new (t : Nat) (x : Item) :
    ∀ cs : List Chunk, x ∉ cs.map Chunk.code → Act.addUse t x cs = cs ++ [⟨x, [t]⟩] := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro hx
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    have hc : c.code ≠ x := fun h => hx.1 h.symm
    simp only [Act.addUse, hc, ite_false, List.cons_append, ih hx.2]

theorem codes_addUse (t : Nat) (x : Item) :
    ∀ cs : List Chunk, ∀ c ∈ (Act.addUse t x cs).map Chunk.code, c = x ∨ c ∈ cs.map Chunk.code := by
  intro cs
  induction cs with
  | nil => intro c hc; simp [Act.addUse] at hc; left; exact hc
  | cons d cs ih =>
    intro c hc
    by_cases hd : d.code = x
    · simp only [Act.addUse, hd, ite_true, List.map_cons, List.mem_cons] at hc
      rcases hc with h | h
      · left; exact h
      · right; simp [h]
    · simp only [Act.addUse, hd, ite_false, List.map_cons, List.mem_cons] at hc
      rcases hc with h | h
      · right; simp [h]
      · rcases ih c h with h' | h'
        · left; exact h'
        · right; simp [h']

theorem studyAll_cons (s : ActState) (x : Item) (xs : List Item) :
    (actRetriever Q).studyAll s (x :: xs) = (actRetriever Q).studyAll (Act.study s x) xs := rfl

/-- Memory holds chunks only for what was there or was studied. -/
theorem codes_studyAll (xs : List Item) :
    ∀ s : ActState, ∀ c ∈ codes ((actRetriever Q).studyAll s xs), c ∈ codes s ∨ c ∈ xs := by
  induction xs with
  | nil => intro s c hc; left; exact hc
  | cons x xs ih =>
    intro s c hc
    rw [studyAll_cons] at hc
    rcases ih (Act.study s x) c hc with h | h
    · rcases codes_addUse s.now x s.chunks c h with h' | h'
      · right; simp [h']
      · left; exact h'
    · right; simp [h]

theorem strengthIn_append {α : Type} (as bs : List α) (w : α → Rat) (e : α → Bool) :
    strengthIn (as ++ bs) w e = strengthIn as w e + strengthIn bs w e := by
  induction as with
  | nil => simp only [List.nil_append, strengthIn]; grind
  | cons a as ih => simp only [List.cons_append, strengthIn, ih]; grind

theorem strengthIn_none {α : Type} (as : List α) (w : α → Rat) (e : α → Bool)
    (h : ∀ a ∈ as, e a = false) : strengthIn as w e = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [strengthIn, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]
    grind

theorem sum_nonneg (l : List Rat) (h : ∀ r ∈ l, 0 ≤ r) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.sum_cons]
    have h1 := h r (List.mem_cons_self ..)
    have h2 := ih fun q hq => h q (List.mem_cons_of_mem r hq)
    grind

theorem pow_pos' (m : Rat) (h : 0 < m) : ∀ k : Nat, 0 < m ^ k
  | 0 => by rw [Rat.pow_zero]; decide
  | k + 1 => by rw [Rat.pow_succ]; exact Rat.mul_pos (pow_pos' m h k) h

theorem baseWeight_nonneg (now : Nat) (uses : List Nat) : 0 ≤ Act.baseWeight now uses := by
  apply sum_nonneg
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨t, _, rfl⟩ := hr
  exact div_nonneg' (by decide) (Rat.natCast_nonneg)

theorem weight_nonneg (s : ActState) (x : Item) (hμ : 0 ≤ Q.mu) (hθ : 0 ≤ Q.theta) :
    ∀ o, 0 ≤ Act.weight Q s x o
  | none => hθ
  | some y => by
    apply sum_nonneg
    intro r hr
    simp only [List.mem_map] at hr
    obtain ⟨c, _, rfl⟩ := hr
    exact Rat.mul_nonneg (baseWeight_nonneg _ _) (Rat.pow_nonneg hμ)

/-- The total weight is positive: failure always has weight. -/
theorem total_pos (s : ActState) (x : Item) (hμ : 0 ≤ Q.mu) (hθ : 0 < Q.theta) :
    0 < total (Act.outcomes s) (Act.weight Q s x) := by
  have h := strengthIn_nonneg (s.chunks.map fun c => some c.code) (Act.weight Q s x)
    (fun _ => true) (weight_nonneg Q s x hμ (Rat.le_of_lt hθ))
  simp only [total, Act.outcomes, strengthIn, ite_true]
  show 0 < Q.theta + _
  grind

/-- The chance of retrieving a code that has exactly one chunk, `c`, among the
last ones. -/
theorem pRet_last (cs : List Chunk) (now : Nat) (c c' : Chunk) (x : Item)
    (hcs : c.code ∉ cs.map Chunk.code) (hc' : c'.code ≠ c.code) :
    (pRet (actRetriever Q) ⟨now, cs ++ [c, c']⟩ x c.code =
      Act.chunkWeight Q now x c / total (Act.outcomes ⟨now, cs ++ [c, c']⟩)
        (Act.weight Q ⟨now, cs ++ [c, c']⟩ x)) ∧
    (pRet (actRetriever Q) ⟨now, cs ++ [c', c]⟩ x c.code =
      Act.chunkWeight Q now x c / total (Act.outcomes ⟨now, cs ++ [c', c]⟩)
        (Act.weight Q ⟨now, cs ++ [c', c]⟩ x)) := by
  have hfil : cs.filter (fun d => d.code == c.code) = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd
    have : d.code ≠ c.code := fun h => hcs (List.mem_map.mpr ⟨d, hd, h⟩)
    simpa using this
  have hcs' : ∀ o ∈ cs.map (fun d => some d.code), (o == some c.code) = false := by
    intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨d, hd, rfl⟩ := ho
    have : d.code ≠ c.code := fun h => hcs (List.mem_map.mpr ⟨d, hd, h⟩)
    simpa using this
  have hne : (c'.code == c.code) = false := by simpa using hc'
  constructor
  · show prob (Act.retrieve Q _ x) _ = _
    rw [Act.prob_retrieve]
    congr 1
    simp only [Act.outcomes, List.map_append, List.map_cons, List.map_nil, strengthIn,
      strengthIn_append, strengthIn_none _ _ _ hcs', Act.weight, List.filter_append, hfil,
      List.filter_cons, hne, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false,
      List.filter_nil, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    grind
  · show prob (Act.retrieve Q _ x) _ = _
    rw [Act.prob_retrieve]
    congr 1
    simp only [Act.outcomes, List.map_append, List.map_cons, List.map_nil, strengthIn,
      strengthIn_append, strengthIn_none _ _ _ hcs', Act.weight, List.filter_append, hfil,
      List.filter_cons, hne, beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false,
      List.filter_nil, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    grind

/-- **Activation has recency**, from an empty memory, for every positive
discount and failure weight: of two stimuli studied last, neither studied
before, a probe equally similar to both retrieves the later twice as often
as the earlier. -/
theorem recency (U : List Item) (hμ : 0 < Q.mu) (hθ : 0 < Q.theta) :
    Recency Q.fs (actRetriever Q) empty U := by
  intro xs _ a _ b _ hab ha hb x hm
  -- The memory before `a` and `b`.
  let s1 := (actRetriever Q).studyAll empty xs
  have hcodes : ∀ c ∈ s1.chunks.map Chunk.code, c ∈ xs := by
    intro c hc
    rcases codes_studyAll Q xs empty c hc with h | h
    · simp [codes, empty] at h
    · exact h
  have ha1 : a ∉ s1.chunks.map Chunk.code := fun h => ha (hcodes a h)
  have hb1 : b ∉ s1.chunks.map Chunk.code := fun h => hb (hcodes b h)
  have hs : (actRetriever Q).studyAll empty (xs ++ [a, b]) =
      ⟨s1.now + 2, s1.chunks ++ [⟨a, [s1.now]⟩, ⟨b, [s1.now + 1]⟩]⟩ := by
    have e1 : (actRetriever Q).studyAll empty (xs ++ [a, b]) =
        Act.study (Act.study s1 a) b := by
      simp only [Retriever.studyAll, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    rw [e1]
    have hb2 : b ∉ (s1.chunks ++ [(⟨a, [s1.now]⟩ : Chunk)]).map Chunk.code := by
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨hb1, fun h => hab h.symm⟩
    simp only [Act.study, addUse_new _ _ _ ha1]
    rw [addUse_new _ _ _ hb2]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hs]
  have hpa := (pRet_last Q s1.chunks (s1.now + 2) ⟨a, [s1.now]⟩ ⟨b, [s1.now + 1]⟩ x ha1
    (fun h => hab h.symm)).1
  have hpb := (pRet_last Q s1.chunks (s1.now + 2) ⟨b, [s1.now + 1]⟩ ⟨a, [s1.now]⟩ x hb1
    hab).2
  simp only at hpa hpb
  rw [hpa, hpb]
  have hT := total_pos Q ⟨s1.now + 2, s1.chunks ++ [⟨a, [s1.now]⟩, ⟨b, [s1.now + 1]⟩]⟩ x
    (Rat.le_of_lt hμ) hθ
  have hpow := pow_pos' Q.mu hμ (mismatches Q.fs x a)
  have hwa : Act.chunkWeight Q (s1.now + 2) x ⟨a, [s1.now]⟩ = 1 / 2 * Q.mu ^ mismatches Q.fs x a := by
    have h2 : s1.now + 2 - s1.now = 2 := by omega
    simp [Act.chunkWeight, Act.baseWeight, h2]
    grind
  have hwb : Act.chunkWeight Q (s1.now + 2) x ⟨b, [s1.now + 1]⟩ = Q.mu ^ mismatches Q.fs x a := by
    have h1 : s1.now + 2 - (s1.now + 1) = 1 := by omega
    simp [Act.chunkWeight, Act.baseWeight, hm, h1]
    grind
  rw [hwa, hwb]
  generalize total _ _ = T at hT ⊢
  generalize Q.mu ^ mismatches Q.fs x a = w at hpow ⊢
  rw [Rat.div_def, Rat.div_def]
  have hT' : 0 < T⁻¹ := Rat.inv_pos.mpr hT
  have : 1 / 2 * w < w := by grind
  exact Rat.mul_lt_mul_of_pos_right this hT'

end Recency

end Cog.Matrix.Activation
