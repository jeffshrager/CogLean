/-
Representations: finite probability distributions.

Some theories say what a system *can* do (EPAM's guesses at a silent cue);
others say how *likely* it is to do it (a child's chance of retrieving an
answer). A finite distribution is a list of outcomes with their
probabilities, exact rationals. Outcomes may repeat: the probability of an
event is the total weight of the outcomes in it.

Results:
* `prob_bind_sum`: the probability of an event after a two-stage process is the
  first stage's probabilities times the second's, summed.
* `prob_bind_ite`: when the second stage's probability takes one value on
  one set of first-stage outcomes and another off it, the whole is a mix of
  the two values, weighted by the first stage.
* `prob_sample`: sampling in proportion to strengths gives an event the
  share of the total strength that lies in it.
-/

namespace Cog

/-- A finite distribution: outcomes with their probabilities. -/
abbrev Dist (α : Type) := List (α × Rat)

namespace Dist

variable {α β : Type}

/-- The distribution certain of `a`. -/
def pure (a : α) : Dist α := [(a, 1)]

/-- A two-stage process: draw `a` from `d`, then draw from `f a`. -/
def bind (d : Dist α) (f : α → Dist β) : Dist β :=
  match d with
  | [] => []
  | (a, p) :: d => ((f a).map fun (b, q) => (b, p * q)) ++ bind d f

/-- The probability of an event. -/
def prob : Dist α → (α → Bool) → Rat
  | [], _ => 0
  | (a, p) :: d, e => (if e a then p else 0) + prob d e

/-- The total probability (1 for a proper distribution). -/
def mass (d : Dist α) : Rat := prob d fun _ => true

/-- `a` can occur: it has positive probability. -/
def Possible (d : Dist α) (a : α) : Prop := ∃ p, (a, p) ∈ d ∧ 0 < p

theorem prob_append (d d' : Dist α) (e : α → Bool) :
    prob (d ++ d') e = prob d e + prob d' e := by
  induction d with
  | nil => simp [prob]; grind
  | cons x d ih => obtain ⟨a, p⟩ := x; simp only [List.cons_append, prob, ih]; grind

theorem prob_scale (d : Dist β) (p : Rat) (e : β → Bool) :
    prob (d.map fun (b, q) => (b, p * q)) e = p * prob d e := by
  induction d with
  | nil => simp [prob]
  | cons x d ih =>
    obtain ⟨b, q⟩ := x
    simp only [List.map_cons, prob, ih]
    split <;> grind

/-- Complementary events share the mass. -/
theorem prob_add_not (d : Dist α) (e : α → Bool) :
    prob d e + prob d (fun a => !e a) = mass d := by
  induction d with
  | nil => simp [mass, prob]; grind
  | cons x d ih =>
    obtain ⟨a, p⟩ := x
    simp only [mass, prob] at ih ⊢
    by_cases h : e a <;> simp [h] <;> grind

theorem prob_pure (a : α) (e : α → Bool) : prob (pure a) e = if e a then 1 else 0 := by
  simp [pure, prob]; split <;> grind

/-- **Two stages.** -/
theorem prob_bind_cons (a : α) (p : Rat) (d : Dist α) (f : α → Dist β) (e : β → Bool) :
    prob (bind ((a, p) :: d) f) e = p * prob (f a) e + prob (bind d f) e := by
  simp [bind, prob_append, prob_scale]

/-- **A two-valued second stage.** If the event has probability `c` after
each first-stage outcome in `g`, and `c'` after each outcome not in it, its
probability overall is `c` times the chance of `g` plus `c'` times the chance
of not `g`. -/
theorem prob_bind_ite (d : Dist α) (f : α → Dist β) (e : β → Bool) (g : α → Bool) (c c' : Rat)
    (hf : ∀ a, prob (f a) e = if g a then c else c') :
    prob (bind d f) e = c * prob d g + c' * prob d (fun a => !g a) := by
  induction d with
  | nil => simp [bind, prob]; grind
  | cons x d ih =>
    obtain ⟨a, p⟩ := x
    rw [prob_bind_cons, ih, hf]
    simp only [prob]
    by_cases h : g a <;> simp [h] <;> grind

/-- **A second stage that is certain on one set and constant on another.** If
the event is certain after first-stage outcomes in `g₁`, has probability `c`
after those in `g₂`, and is impossible otherwise, its probability overall is
the chance of `g₁` plus `c` times the chance of `g₂`. -/
theorem prob_bind_split (d : Dist α) (f : α → Dist β) (e : β → Bool) (g₁ g₂ : α → Bool) (c : Rat)
    (hf : ∀ a, prob (f a) e = (if g₁ a then 1 else 0) + (if g₂ a then c else 0)) :
    prob (bind d f) e = prob d g₁ + c * prob d g₂ := by
  induction d with
  | nil => simp [bind, prob]; grind
  | cons x d ih =>
    obtain ⟨a, p⟩ := x
    rw [prob_bind_cons, ih, hf]
    simp only [prob]
    by_cases h₁ : g₁ a <;> by_cases h₂ : g₂ a <;> simp [h₁, h₂] <;> grind

/-- Drawing from a certain distribution is just applying the second stage. -/
theorem bind_pure_left (a : α) (f : α → Dist β) : bind (pure a) f = f a := by
  simp only [bind, pure, List.append_nil]
  conv => rhs; rw [← List.map_id (f a)]
  apply List.map_congr_left
  intro x _
  obtain ⟨b, q⟩ := x
  simp [Rat.one_mul]

theorem bind_append {γ : Type} (d d' : Dist α) (f : α → Dist γ) :
    bind (d ++ d') f = bind d f ++ bind d' f := by
  induction d with
  | nil => rfl
  | cons x d ih => obtain ⟨a, p⟩ := x; simp [bind, ih]

theorem bind_scale {γ : Type} (d : Dist α) (p : Rat) (f : α → Dist γ) :
    bind (d.map fun (b, q) => (b, p * q)) f =
      (bind d f).map fun (c, r) => (c, p * r) := by
  induction d with
  | nil => rfl
  | cons x d ih =>
    obtain ⟨a, q⟩ := x
    simp only [List.map_cons, bind, ih, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro y _
    obtain ⟨c, r⟩ := y
    simp [Rat.mul_assoc]

/-- **Two-stage draws regroup.** -/
theorem bind_assoc {γ : Type} (d : Dist α) (f : α → Dist β) (g : β → Dist γ) :
    bind (bind d f) g = bind d fun a => bind (f a) g := by
  induction d with
  | nil => rfl
  | cons x d ih =>
    obtain ⟨a, p⟩ := x
    simp only [bind, bind_append, ih, bind_scale]

/-- Drawing and then certainly keeping the draw changes nothing. -/
theorem bind_pure_right (d : Dist α) : bind d pure = d := by
  induction d with
  | nil => rfl
  | cons x d ih => obtain ⟨a, p⟩ := x; simp [bind, pure, ih, Rat.mul_one]

theorem bind_congr {γ : Type} (d : Dist α) (f g : α → Dist γ) (h : ∀ a, f a = g a) :
    bind d f = bind d g := by
  have : f = g := funext h
  rw [this]

/-- **Relabelling.** Drawing from `d` and then certainly giving `g a` is
drawing from `d` and asking of `g a`. -/
theorem prob_bind_pure (d : Dist α) (g : α → β) (e : β → Bool) :
    prob (bind d fun a => pure (g a)) e = prob d (fun a => e (g a)) := by
  induction d with
  | nil => simp [bind, prob]
  | cons x d ih =>
    obtain ⟨a, p⟩ := x
    rw [prob_bind_cons, ih, prob_pure]
    simp only [prob]
    split <;> grind

/-- The impossible event. -/
theorem prob_false (d : Dist α) : prob d (fun _ => false) = 0 := by
  induction d with
  | nil => rfl
  | cons x d ih => obtain ⟨a, p⟩ := x; simp [prob, ih]; grind

/-- The probability of an event is unchanged by an event that agrees with it
on every outcome. -/
theorem prob_congr (d : Dist α) (e e' : α → Bool) (h : ∀ a, e a = e' a) :
    prob d e = prob d e' := by
  have : e = e' := funext h
  rw [this]

/-- **A mixture.** The probability of an event after a two-stage process is
the sum, over first-stage outcomes, of each one's probability times the
event's probability after it. -/
theorem prob_bind_sum (d : Dist α) (f : α → Dist β) (e : β → Bool) :
    prob (bind d f) e = (d.map fun ap => ap.2 * prob (f ap.1) e).sum := by
  induction d with
  | nil => simp [bind, prob]
  | cons x d ih => obtain ⟨a, p⟩ := x; rw [prob_bind_cons, ih]; simp

theorem pure_inj {a b : α} (h : pure a = pure b) : a = b := by
  simp [pure] at h; exact h

/-- Only `a` can occur in the distribution certain of `a`. -/
theorem possible_pure {a b : α} : Possible (pure a) b ↔ b = a := by
  constructor
  · rintro ⟨p, hp, _⟩
    simp [pure] at hp
    exact hp.1
  · intro h
    exact ⟨1, by simp [pure, h], by decide⟩

/-- **Proper stages make a proper process.** If the first stage and every
second stage are proper distributions, so is the two-stage process. -/
theorem mass_bind (d : Dist α) (f : α → Dist β) (hd : mass d = 1) (hf : ∀ a, mass (f a) = 1) :
    mass (bind d f) = 1 := by
  simp only [mass] at hd hf ⊢
  rw [prob_bind_split d f _ (fun _ => true) (fun _ => false) 0 (fun a => by simp [hf a]; grind)]
  rw [hd]; grind

theorem mass_pure (a : α) : mass (pure a) = 1 := by simp [mass, prob_pure]

/-- Every weight is nonnegative. A list with nonnegative weights and mass 1 is
a probability distribution; mass 1 alone does not rule out negative weights. -/
def Nonneg (d : Dist α) : Prop := ∀ ap ∈ d, 0 ≤ ap.2

theorem nonneg_pure (a : α) : Nonneg (pure a) := by
  intro ap h
  simp only [pure, List.mem_singleton] at h
  rw [h]; show (0 : Rat) ≤ 1; decide +kernel

/-- **Nonnegative stages make a nonnegative process.** -/
theorem nonneg_bind (d : Dist α) (f : α → Dist β) (hd : Nonneg d) (hf : ∀ a, Nonneg (f a)) :
    Nonneg (bind d f) := by
  induction d with
  | nil => intro ap h; simp [bind] at h
  | cons x d ih =>
    obtain ⟨a, p⟩ := x
    intro bq h
    simp only [bind, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨b, q⟩, hm, rfl⟩ | h
    · exact Rat.mul_nonneg (hd _ List.mem_cons_self) (hf a _ hm)
    · exact ih (fun y hy => hd y (List.mem_cons_of_mem _ hy)) bq h

/-! ### Merging equal outcomes

Outcomes may repeat, so a many-stage process can be a long list. `merge`
adds up the weights of equal outcomes. It changes no probability, before or
after a further stage (`prob_bind_merge`), so a merged distribution can stand
in for the original wherever only probabilities matter. -/

/-- The weighted average of `h` over `d`. -/
def expect (d : Dist α) (h : α → Rat) : Rat := (d.map fun ap => ap.2 * h ap.1).sum

/-- Add weight `p` to outcome `a`. -/
def addTo [DecidableEq α] (a : α) (p : Rat) : Dist α → Dist α
  | [] => [(a, p)]
  | (b, q) :: d => if a = b then (b, q + p) :: d else (b, q) :: addTo a p d

/-- Equal outcomes, merged. -/
def merge [DecidableEq α] : Dist α → Dist α
  | [] => []
  | (a, p) :: d => addTo a p (merge d)

theorem expect_addTo [DecidableEq α] (a : α) (p : Rat) (h : α → Rat) (d : Dist α) :
    expect (addTo a p d) h = p * h a + expect d h := by
  induction d with
  | nil => simp [addTo, expect]
  | cons x d ih =>
    obtain ⟨b, q⟩ := x
    by_cases hab : a = b
    · subst hab; simp [addTo, expect, Rat.add_mul]; grind
    · simp only [addTo, hab, ite_false]
      simp only [expect, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; grind

theorem expect_merge [DecidableEq α] (d : Dist α) (h : α → Rat) :
    expect (merge d) h = expect d h := by
  induction d with
  | nil => rfl
  | cons x d ih =>
    obtain ⟨a, p⟩ := x
    simp only [merge, expect_addTo, ih]
    simp [expect]

/-- **Merging changes no probability**, even after a further stage. -/
theorem prob_bind_merge [DecidableEq α] (d : Dist α) (f : α → Dist β) (e : β → Bool) :
    prob (bind (merge d) f) e = prob (bind d f) e := by
  rw [prob_bind_sum, prob_bind_sum]
  exact expect_merge d fun a => prob (f a) e

theorem prob_merge [DecidableEq α] (d : Dist α) (e : α → Bool) : prob (merge d) e = prob d e := by
  have h := prob_bind_merge d pure e
  rwa [bind_pure_right, bind_pure_right] at h

/-- A second stage enters an event's probability only through that event's
probability after each first-stage outcome. -/
theorem prob_bind_congr {γ : Type} (d : Dist α) (f g : α → Dist γ) (e : γ → Bool)
    (h : ∀ a, prob (f a) e = prob (g a) e) : prob (bind d f) e = prob (bind d g) e := by
  rw [prob_bind_sum, prob_bind_sum]
  congr 1
  apply List.map_congr_left
  intro x _
  rw [h]

/-- Two lists are the **same distribution** when every weighted average,
and so every probability, agrees on them, however their outcomes are listed. -/
def Same (d d' : Dist α) : Prop := ∀ h : α → Rat, expect d h = expect d' h

theorem prob_eq_expect (d : Dist α) (e : α → Bool) :
    prob d e = expect d fun a => if e a then 1 else 0 := by
  induction d with
  | nil => rfl
  | cons x d ih =>
    obtain ⟨a, p⟩ := x
    simp only [prob, ih, expect, List.map_cons, List.sum_cons]
    split <;> grind

theorem Same.prob {d d' : Dist α} (h : Same d d') (e : α → Bool) : prob d e = prob d' e := by
  rw [prob_eq_expect, prob_eq_expect, h]

theorem Same.refl (d : Dist α) : Same d d := fun _ => rfl

theorem same_merge [DecidableEq α] (d : Dist α) : Same (merge d) d := expect_merge d

theorem expect_bind (d : Dist α) (f : α → Dist β) (h : β → Rat) :
    expect (bind d f) h = expect d fun a => expect (f a) h := by
  induction d with
  | nil => rfl
  | cons x d ih =>
    obtain ⟨a, p⟩ := x
    have hs : ∀ l : Dist β, ((l.map fun (b, q) => (b, p * q)).map fun bq => bq.2 * h bq.1).sum =
        p * (l.map fun bq => bq.2 * h bq.1).sum := by
      intro l
      induction l with
      | nil => simp
      | cons y l ihl => obtain ⟨b, q⟩ := y; simp only [List.map_cons, List.sum_cons] at ihl ⊢; rw [ihl]; grind
    simp only [bind, expect, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, hs]

/-- **Same stages, same process.** -/
theorem same_bind {d d' : Dist α} {f g : α → Dist β} (hd : Same d d') (hf : ∀ a, Same (f a) (g a)) :
    Same (bind d f) (bind d' g) := by
  intro h
  rw [expect_bind, expect_bind, hd]
  have : (fun a => expect (f a) h) = (fun a => expect (g a) h) := funext fun a => hf a h
  rw [this]

/-! ### Sampling in proportion to strength -/

/-- The total strength of the outcomes in `as` that satisfy `e`. -/
def strengthIn (as : List α) (s : α → Rat) (e : α → Bool) : Rat :=
  match as with
  | [] => 0
  | a :: as => (if e a then s a else 0) + strengthIn as s e

/-- The total strength of `as`. -/
def total (as : List α) (s : α → Rat) : Rat := strengthIn as s fun _ => true

/-- Draw one of `as`, each with probability proportional to its strength. -/
def sample (as : List α) (s : α → Rat) : Dist α :=
  as.map fun a => (a, s a / total as s)

theorem prob_map_div (as : List α) (s : α → Rat) (T : Rat) (e : α → Bool) :
    prob (as.map fun a => (a, s a / T)) e = strengthIn as s e / T := by
  induction as with
  | nil => simp [prob, strengthIn]; grind
  | cons a as ih =>
    simp only [List.map_cons, prob, strengthIn, ih]
    split <;> grind

/-- **Sampling.** An event's probability is its share of the total
strength. -/
theorem prob_sample (as : List α) (s : α → Rat) (e : α → Bool) :
    prob (sample as s) e = strengthIn as s e / total as s :=
  prob_map_div as s _ e

/-- A sample from positive total strength is a proper distribution. -/
theorem mass_sample (as : List α) (s : α → Rat) (hT : total as s ≠ 0) :
    mass (sample as s) = 1 := by
  rw [mass, prob_sample]
  exact (by grind : ∀ T : Rat, T ≠ 0 → T / T = 1) _ hT

theorem div_nonneg' {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [Rat.div_def]
  apply Rat.mul_nonneg ha
  by_cases h : b = 0
  · subst h; rw [Rat.inv_zero]; exact Rat.le_refl
  · exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.lt_of_le_of_ne hb (Ne.symm h)))

/-- Comparing quotients by cross-multiplying. -/
theorem div_le_div_cross {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  have hb' : b ≠ 0 := by grind
  have hd' : d ≠ 0 := by grind
  have e1 : a / b = (a * d) * (b * d)⁻¹ := by grind
  have e2 : c / d = (c * b) * (b * d)⁻¹ := by grind
  rw [e1, e2]
  apply Rat.mul_le_mul_of_nonneg_right h
  exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hb hd))

theorem strengthIn_nonneg (as : List α) (s : α → Rat) (e : α → Bool) (hs : ∀ a, 0 ≤ s a) :
    0 ≤ strengthIn as s e := by
  induction as with
  | nil => simp [strengthIn]
  | cons a as ih =>
    simp only [strengthIn]
    have := hs a
    split <;> grind

/-- Splitting an event by a second test. -/
theorem strengthIn_split (as : List α) (s : α → Rat) (e g : α → Bool) :
    strengthIn as s e =
      strengthIn as s (fun a => e a && g a) + strengthIn as s (fun a => e a && !g a) := by
  induction as with
  | nil => simp [strengthIn]; grind
  | cons a as ih =>
    simp only [strengthIn, ih]
    by_cases he : e a <;> by_cases hg : g a <;> simp [he, hg] <;> grind

/-- **Less strength, in a smaller event, is less total strength.** If every
outcome in `e'` under strengths `s'` is in `e` with at least as much strength
under `s`, the total strength of `e'` under `s'` is at most that of `e` under
`s`. -/
theorem strengthIn_mono (as : List α) (s s' : α → Rat) (e e' : α → Bool)
    (hs : ∀ a, 0 ≤ s a) (h : ∀ a, e' a = true → e a = true ∧ s' a ≤ s a) :
    strengthIn as s' e' ≤ strengthIn as s e := by
  induction as with
  | nil => simp [strengthIn]
  | cons a as ih =>
    simp only [strengthIn]
    have := hs a
    by_cases he' : e' a
    · obtain ⟨he, hle⟩ := h a he'
      simp [he, he']; grind
    · simp [he']
      by_cases he : e a <;> simp [he] <;> grind

theorem strengthIn_le_total (as : List α) (s : α → Rat) (e : α → Bool) (hs : ∀ a, 0 ≤ s a) :
    strengthIn as s e ≤ total as s := by
  induction as with
  | nil => simp [total, strengthIn]
  | cons a as ih =>
    simp only [total, strengthIn] at ih ⊢
    have := hs a
    split <;> grind

/-- Sampling from nonnegative strengths gives nonnegative weights. -/
theorem nonneg_sample (as : List α) (s : α → Rat) (hs : ∀ a, 0 ≤ s a) : Nonneg (sample as s) := by
  intro ap h
  simp only [sample, List.mem_map] at h
  obtain ⟨a, _, rfl⟩ := h
  exact div_nonneg' (hs a) (strengthIn_nonneg as s _ hs)

end Dist
end Cog
