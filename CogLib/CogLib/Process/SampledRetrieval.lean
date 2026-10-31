/-
Processes: retrieval by sampling, with a confidence criterion and a search
length.

Answers are associated with a problem with varying strengths. A search
draws one answer, with probability proportional to its strength, and states
it if its strength exceeds a *confidence criterion*. If not, search again,
up to a *search length*; if none is stated, retrieval is exhausted and some
other process (a backup strategy) has to produce the answer.

Write `R` for the chance that one search finds an answer above the
criterion. Then:

* `prob_exhausted`: retrieval is exhausted with probability `(1 - R)^n`
  after a search length `n`.
* `prob_stated`: an answer with a property `P` is stated with probability
  `Q · (1 + (1-R) + ... + (1-R)^(n-1))`, where `Q` is the chance that one
  search finds an answer above the criterion with `P`.
* `stated_share`: among stated answers, the share with `P` is `Q / R`, the
  same for every search length.
* `exhausted_antitone_reach`, `exhausted_antitone_length`: the more often a
  search reaches the criterion, and the longer the search, the less often
  retrieval is exhausted.
* `stated_share_shift`, `aboveShare_shift`: moving strength towards one
  answer (from any of the others) never raises the share of the others among
  stated answers, at any criterion.
-/

import CogLib.Rep.Distribution

namespace Cog

/-- The result of retrieval: an answer stated after some number of searches,
or nothing stated within the search length. -/
inductive Retrieval (α : Type) where
  | stated : α → Nat → Retrieval α
  | exhausted : Retrieval α
  deriving Repr, DecidableEq

namespace Retrieval

variable {α : Type}

def isExhausted : Retrieval α → Bool
  | exhausted => true
  | stated _ _ => false

/-- An answer with property `P` was stated. -/
def statedSuch (P : α → Bool) : Retrieval α → Bool
  | stated a _ => P a
  | exhausted => false

end Retrieval

open Dist

variable {α : Type}

/-- The answer's strength exceeds the confidence criterion. -/
def above (s : α → Rat) (cc : Rat) (a : α) : Bool := decide (cc < s a)

/-- Retrieval among answers `as` with strengths `s`, confidence criterion
`cc`, and `n` searches left, `k` having been made. -/
def search (as : List α) (s : α → Rat) (cc : Rat) : Nat → Nat → Dist (Retrieval α)
  | _, 0 => Dist.pure .exhausted
  | k, n + 1 => Dist.bind (sample as s) fun a =>
      if above s cc a then Dist.pure (.stated a (k + 1)) else search as s cc (k + 1) n

/-- The chance that one search finds an answer above the criterion. -/
def reach (as : List α) (s : α → Rat) (cc : Rat) : Rat := prob (sample as s) (above s cc)

/-- The chance that one search finds an answer above the criterion with
property `P`. -/
def reachSuch (as : List α) (s : α → Rat) (cc : Rat) (P : α → Bool) : Rat :=
  prob (sample as s) fun a => above s cc a && P a

/-- `1 + x + ... + x^(n-1)`. -/
def geom (x : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => 1 + x * geom x n

theorem prob_not_above (as : List α) (s : α → Rat) (cc : Rat) (hT : total as s ≠ 0) :
    prob (sample as s) (fun a => !above s cc a) = 1 - reach as s cc := by
  have h := prob_add_not (sample as s) (above s cc)
  rw [mass_sample as s hT] at h
  simp only [reach]; grind

/-- Retrieval from positive total strength is a proper distribution. -/
theorem mass_search (as : List α) (s : α → Rat) (cc : Rat) (hT : total as s ≠ 0) :
    ∀ n k, mass (search as s cc k n) = 1 := by
  intro n
  induction n with
  | zero => intro k; exact mass_pure _
  | succ n ih =>
    intro k
    simp only [search]
    apply mass_bind _ _ (mass_sample as s hT)
    intro a
    split
    · exact mass_pure _
    · exact ih _

/-- Retrieval from nonnegative strengths has nonnegative weights. -/
theorem nonneg_search (as : List α) (s : α → Rat) (cc : Rat) (hs : ∀ a, 0 ≤ s a) :
    ∀ n k, Nonneg (search as s cc k n) := by
  intro n
  induction n with
  | zero => intro k; exact nonneg_pure _
  | succ n ih =>
    intro k
    simp only [search]
    apply nonneg_bind _ _ (nonneg_sample as s hs)
    intro a
    split
    · exact nonneg_pure _
    · exact ih _

/-- **Exhaustion.** With search length `n`, retrieval is exhausted with
probability `(1 - R)^n`. -/
theorem prob_exhausted (as : List α) (s : α → Rat) (cc : Rat) (hT : total as s ≠ 0) :
    ∀ n k, prob (search as s cc k n) Retrieval.isExhausted = (1 - reach as s cc) ^ n := by
  intro n
  induction n with
  | zero => intro k; simp [search, prob_pure, Retrieval.isExhausted]
  | succ n ih =>
    intro k
    simp only [search]
    rw [prob_bind_split _ _ _ (fun _ => false) (fun a => !above s cc a) ((1 - reach as s cc) ^ n)]
    · rw [prob_false, prob_not_above as s cc hT, Rat.pow_succ]; grind
    · intro a
      by_cases ha : above s cc a
      · simp [ha, prob_pure, Retrieval.isExhausted]; grind
      · simp [ha, ih]; grind

/-- **Stating an answer.** With search length `n`, an answer with property `P`
is stated with probability `Q · geom (1 - R) n`. -/
theorem prob_stated (as : List α) (s : α → Rat) (cc : Rat) (P : α → Bool)
    (hT : total as s ≠ 0) :
    ∀ n k, prob (search as s cc k n) (Retrieval.statedSuch P) =
      reachSuch as s cc P * geom (1 - reach as s cc) n := by
  intro n
  induction n with
  | zero => intro k; simp [search, prob_pure, Retrieval.statedSuch, geom]
  | succ n ih =>
    intro k
    simp only [search]
    rw [prob_bind_split _ _ _ (fun a => above s cc a && P a) (fun a => !above s cc a)
      (reachSuch as s cc P * geom (1 - reach as s cc) n)]
    · rw [prob_not_above as s cc hT]
      simp only [reachSuch, geom]
      grind
    · intro a
      by_cases ha : above s cc a
      · by_cases hp : P a <;> simp [ha, hp, prob_pure, Retrieval.statedSuch] <;> grind
      · simp [ha, ih]; grind

/-- **The share of stated answers with `P` does not depend on the search
length.** Stated answers have `P` in proportion `Q / R`: the probability of
stating one with `P`, times `R`, equals the probability of stating any, times
`Q`. -/
theorem stated_share (as : List α) (s : α → Rat) (cc : Rat) (P : α → Bool)
    (hT : total as s ≠ 0) (n k : Nat) :
    prob (search as s cc k n) (Retrieval.statedSuch P) * reach as s cc =
      prob (search as s cc k n) (Retrieval.statedSuch fun _ => true) * reachSuch as s cc P := by
  rw [prob_stated as s cc P hT, prob_stated as s cc _ hT]
  have : reachSuch as s cc (fun _ => true) = reach as s cc := by
    simp only [reachSuch, reach, Bool.and_true]
  rw [this]; grind

theorem pow_le_pow_of_le {x y : Rat} (n : Nat) (h0 : 0 ≤ x) (h : x ≤ y) : x ^ n ≤ y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Rat.pow_succ, Rat.pow_succ]
    have hx : 0 ≤ x ^ n := Rat.pow_nonneg h0
    have hy : 0 ≤ y ^ n := Rat.le_trans hx ih
    have h1 : x ^ n * x ≤ y ^ n * x := Rat.mul_le_mul_of_nonneg_right ih h0
    have h2 : y ^ n * x ≤ y ^ n * y := Rat.mul_le_mul_of_nonneg_left h hy
    exact Rat.le_trans h1 h2

/-- **Reaching the criterion more often, retrieval is exhausted less
often.** -/
theorem exhausted_antitone_reach {R R' : Rat} (n : Nat) (hR : R ≤ R') (h1 : R' ≤ 1) :
    (1 - R') ^ n ≤ (1 - R) ^ n :=
  pow_le_pow_of_le n (by grind) (by grind)

/-- **Searching longer, retrieval is exhausted less often.** -/
theorem exhausted_antitone_length {R : Rat} (n : Nat) (h0 : 0 ≤ R) (h1 : R ≤ 1) :
    (1 - R) ^ (n + 1) ≤ (1 - R) ^ n := by
  rw [Rat.pow_succ]
  have hx : 0 ≤ (1 - R) ^ n := Rat.pow_nonneg (by grind)
  have := Rat.mul_le_mul_of_nonneg_left (show 1 - R ≤ 1 by grind) hx
  grind

theorem reach_nonneg (as : List α) (s : α → Rat) (cc : Rat) (hs : ∀ a, 0 ≤ s a) :
    0 ≤ reach as s cc := by
  rw [reach, prob_sample]
  have h1 := strengthIn_nonneg as s (above s cc) hs
  have h2 := strengthIn_nonneg as s (fun _ => true) hs
  exact div_nonneg' h1 h2

theorem reach_le_one (as : List α) (s : α → Rat) (cc : Rat) (hs : ∀ a, 0 ≤ s a)
    (hT : total as s ≠ 0) : reach as s cc ≤ 1 := by
  have h := prob_add_not (sample as s) (above s cc)
  rw [mass_sample as s hT] at h
  have : 0 ≤ prob (sample as s) (fun a => !above s cc a) := by
    rw [prob_sample]
    exact div_nonneg' (strengthIn_nonneg as s _ hs) (strengthIn_nonneg as s _ hs)
  simp only [reach]; grind

/-- **Shifting strength towards an answer never raises the share of the
others among stated answers.** Suppose strengths `s'` give the answer `c` at
least the strength `s` gives it, and every other answer at most. Then, at any
confidence criterion, the others' share of the stated answers is no larger
under `s'` than under `s` (cross-multiplied: `W' · R ≤ W · R'`). -/
theorem stated_share_shift [DecidableEq α] (as : List α) (s s' : α → Rat) (cc : Rat) (c : α)
    (hs : ∀ a, 0 ≤ s a) (hs' : ∀ a, 0 ≤ s' a)
    (hc : s c ≤ s' c) (hother : ∀ a, a ≠ c → s' a ≤ s a) :
    strengthIn as s' (fun a => above s' cc a && a != c) * strengthIn as s (above s cc) ≤
      strengthIn as s (fun a => above s cc a && a != c) * strengthIn as s' (above s' cc) := by
  -- W = wrong strength above the criterion, C = correct strength above it.
  have hW : strengthIn as s' (fun a => above s' cc a && a != c) ≤
      strengthIn as s (fun a => above s cc a && a != c) := by
    apply strengthIn_mono as s s' _ _ hs
    intro a ha
    simp only [above, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at ha ⊢
    have := hother a ha.2
    exact ⟨⟨by grind, ha.2⟩, this⟩
  have hC : strengthIn as s (fun a => above s cc a && !(a != c)) ≤
      strengthIn as s' (fun a => above s' cc a && !(a != c)) := by
    apply strengthIn_mono as s' s _ _ hs'
    intro a ha
    simp only [above, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', bne_eq_false_iff_eq]
      at ha ⊢
    obtain ⟨h1, rfl⟩ := ha
    exact ⟨⟨by grind, rfl⟩, hc⟩
  rw [strengthIn_split as s (above s cc) (fun a => a != c),
    strengthIn_split as s' (above s' cc) (fun a => a != c)]
  have w0 := strengthIn_nonneg as s' (fun a => above s' cc a && a != c) hs'
  have c0 := strengthIn_nonneg as s (fun a => above s cc a && !(a != c)) hs
  generalize strengthIn as s' (fun a => above s' cc a && a != c) = W' at *
  generalize strengthIn as s (fun a => above s cc a && a != c) = W at *
  generalize strengthIn as s (fun a => above s cc a && !(a != c)) = C at *
  generalize strengthIn as s' (fun a => above s' cc a && !(a != c)) = C' at *
  -- W' (W + C) ≤ W (W' + C')  ⇐  W' ≤ W, C ≤ C'
  have h1 : W' * C ≤ W * C := Rat.mul_le_mul_of_nonneg_right hW c0
  have h2 : W * C ≤ W * C' := Rat.mul_le_mul_of_nonneg_left hC (Rat.le_trans w0 hW)
  grind

/-- Retrieval either states an answer or is exhausted:
`R · geom (1 - R) n = 1 - (1 - R)^n`. -/
theorem reach_mul_geom (R : Rat) : ∀ n, R * geom (1 - R) n = 1 - (1 - R) ^ n := by
  intro n
  induction n with
  | zero => simp [geom]; grind
  | succ n ih =>
    simp only [geom, Rat.pow_succ]
    have : R * (1 + (1 - R) * geom (1 - R) n) = R + (1 - R) * (R * geom (1 - R) n) := by grind
    rw [this, ih]; grind

/-- The share, among the strength above the criterion, of the answers with
`P`. By `stated_share` and `reachSuch_div_reach`, it is the share of stated
answers with `P`. -/
def aboveShare (as : List α) (s : α → Rat) (cc : Rat) (P : α → Bool) : Rat :=
  strengthIn as s (fun a => above s cc a && P a) / strengthIn as s (above s cc)

theorem reachSuch_div_reach (as : List α) (s : α → Rat) (cc : Rat) (P : α → Bool)
    (hT : total as s ≠ 0) (hR : strengthIn as s (above s cc) ≠ 0) :
    reachSuch as s cc P / reach as s cc = aboveShare as s cc P := by
  simp only [reachSuch, reach, aboveShare, prob_sample]
  grind

/-- **Shifting strength towards an answer never raises the others' share**
of the strength above any criterion (so of stated answers). -/
theorem aboveShare_shift [DecidableEq α] (as : List α) (s s' : α → Rat) (cc : Rat) (c : α)
    (hs : ∀ a, 0 ≤ s a) (hs' : ∀ a, 0 ≤ s' a)
    (hc : s c ≤ s' c) (hother : ∀ a, a ≠ c → s' a ≤ s a)
    (hR : 0 < strengthIn as s (above s cc)) (hR' : 0 < strengthIn as s' (above s' cc)) :
    aboveShare as s' cc (fun a => a != c) ≤ aboveShare as s cc (fun a => a != c) :=
  div_le_div_cross hR' hR (stated_share_shift as s s' cc c hs hs' hc hother)

end Cog
