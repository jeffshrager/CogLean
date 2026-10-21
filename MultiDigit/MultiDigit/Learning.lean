/-
Learning in the multi-digit model (M5).

Two kinds of learning are in play. EPAM's discrimination learning grows the
net when a problem is confused with another. DOA's strengthening adds to the
associations of every answer stated (`SC.strengthen`, with its theorem
`SC.correct_strengthening_lowers_errors`).

Results:
* `near_miss_200_learned`, `near_miss_20_learned`: for any net EPAM learns
  from an empty one, the near-miss predictions hold with no extra hypothesis
  (such nets store each image once: `learnAll_clean`).
* `discrimination_removes_confusion`: after a confused problem is learned,
  it is recognized as itself and retrieved from its own associations, and
  the problem it was confused with is untouched.
* `discrimination_then_columns`: a newly discriminated problem whose
  associations do not yet clear the criterion is worked out by the columns
  on every trial. A confident error is followed, after discrimination, by
  slow column work, before the new associations are strengthened.
-/

import MultiDigit.Phenomena

namespace MD

open Cog Dist

variable (E : Encoding) (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat)
  (backup : Problem → Dist Nat)

/-- In a clean net, what a code is recognized as is recognized as itself. -/
theorem clean_target {N : Net} (hc : Net.Clean N) {x y : Item} (h : N.select x = some y) :
    N.select y = some y :=
  hc.2 y (Net.select_mem_images N x y h)

/-- **Near misses within 200, for any net EPAM learns from empty.** -/
theorem near_miss_200_learned (order : NoticingOrder) (xs : List Item) (x q : Problem)
    (hx : (Net.learnAll order (Net.leaf none) xs).select (E.code x) = some (E.code q))
    (hcover : ∀ i, ∀ f ∈ E.features i .hundreds,
      f ∈ (Net.learnAll order (Net.leaf none) xs).path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 200 ∧ x.sum < q.sum + 200 := by
  have hc := Net.learnAll_clean order xs _ Net.clean_empty
  exact near_miss_200 E _ x q hc.1 (clean_target hc hx) hx hcover hxa hxb hqa hqb

/-- **Near misses within 20, for any net EPAM learns from empty.** -/
theorem near_miss_20_learned (order : NoticingOrder) (xs : List Item) (x q : Problem)
    (hx : (Net.learnAll order (Net.leaf none) xs).select (E.code x) = some (E.code q))
    (hcover : ∀ i, ∀ j, j ≠ Place.units → ∀ f ∈ E.features i j,
      f ∈ (Net.learnAll order (Net.leaf none) xs).path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 20 ∧ x.sum < q.sum + 20 := by
  have hc := Net.learnAll_clean order xs _ Net.clean_empty
  exact near_miss_20 E _ x q hc.1 (clean_target hc hx) hx hcover hxa hxb hqa hqb

/-- **Discrimination removes a confusion, and only that.** Let `x` be confused
with `q` in a clean net, and let `x`'s code be noticeably different from
every stored image. After EPAM learns `x`:

* `x` is recognized as itself, and whole-problem retrieval on it uses its own
  associations;
* `q`'s trial is exactly what it was;
* the net is still clean. -/
theorem discrimination_removes_confusion (order : NoticingOrder) (N : Net) (x q : Problem)
    (hc : Net.Clean N) (hx : N.select (E.code x) = some (E.code q))
    (hne : E.code q ≠ E.code x)
    (hn : ∀ z ∈ N.images, z ≠ E.code x → Noticeable order (E.code x) z) :
    let N' := N.learn order (E.code x)
    N'.select (E.code x) = some (E.code x) ∧
      (∀ P, prob (trial E N' str as cc n backup x) (wholeSuch P) =
        prob (search as (str (E.code x)) cc 0 n) (Retrieval.statedSuch P)) ∧
      trial E N' str as cc n backup q = trial E N str as cc n backup q ∧
      Net.Clean N' := by
  intro N'
  have hself : N'.select (E.code x) = some (E.code x) := Net.learn_recognizes order N _ hn
  refine ⟨hself, fun P => whole_depends_only_on_route E N' str as cc n backup x _ P hself, ?_,
    Net.learn_clean order N _ hc⟩
  exact learning_preserves_trial E N str as cc n backup order q _ (clean_target hc hx) hne

/-- **After discrimination, the columns.** A problem recognized as itself
whose own associations do not yet clear the criterion falls back on the
columns on every trial. -/
theorem discrimination_then_columns (N : Net) (x : Problem) (hT : ∀ y, total as (str y) ≠ 0)
    (hb : mass (backup x) = 1) (hself : N.select (E.code x) = some (E.code x))
    (hlow : ∀ a, str (E.code x) a ≤ cc) :
    prob (trial E N str as cc n backup x) isColumns = 1 := by
  rw [columns_prob E N str as cc n backup x hb hT, hself]
  simp only
  have hfalse : ∀ l : List Nat, strengthIn l (str (E.code x)) (fun _ => false) = 0 := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [strengthIn, ih]; grind
  have habove : above (str (E.code x)) cc = fun _ => false := by
    funext a; simp only [above, decide_eq_false_iff_not]; have := hlow a; grind
  have hR : reach as (str (E.code x)) cc = 0 := by
    simp only [reach, prob_sample, habove, hfalse]; grind
  rw [hR, show (1 : Rat) - 0 = 1 by grind]
  clear hR habove hfalse hself hb hT hlow
  induction n with
  | zero => simp
  | succ n ih => rw [Rat.pow_succ, ih]; grind

end MD
