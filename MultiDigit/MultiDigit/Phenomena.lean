/-
What the combined model predicts, deduced from its postulates.

Every theorem holds for any encoding, net, strengths, criterion, search
length and backup. Each is proved by composing results already proved for
EPAM's discrimination nets and for DOA retrieval (in CogLib).

* `columns_prob` (strategy nesting): the column backup is used with
  probability 1 if the problem is not recognized, and `(1 - R_y)^n` if it is
  recognized as `y`.
* `whole_depends_only_on_route`: whole-problem retrieval on `x` behaves
  exactly as retrieval on whatever `x` is recognized as.
* `confusion_gives_neighbours_answer`: a problem confused with `q`, where
  only `q`'s sum clears the criterion, gets `q`'s sum on every
  whole-problem retrieval trial.
* `confident_errors`: such a confusion makes every retrieval trial an error,
  while backup use stays as low as on `q` itself, where retrieval never errs.
  DOA alone ties errors to backup use; confusion breaks the tie.
* `same_sum_confusion_harmless`, `commuted_confusion_harmless`: confusion
  with a problem of the same sum (for example the commuted problem) costs
  nothing.
* `near_miss_200`, `near_miss_20`: if a confused problem's path tests the
  hundreds digits (and the tens digits), its answer is within 200 (within
  20) of the right one.
* `learning_preserves_trial`: learning other problems never changes how a
  studied problem is answered.
-/

import MultiDigit.Postulates

namespace MD

open Cog Dist

variable (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat)
  (backup : Problem → Dist Nat)

/-- The column backup, as part of a trial, makes every outcome a column
outcome. -/
theorem prob_backup_part (x : Problem) (e : Route × Nat → Bool) :
    prob (Dist.bind (backup x) fun r => Dist.pure (Route.columns, r)) e =
      prob (backup x) (fun r => e (.columns, r)) :=
  prob_bind_pure _ _ _

/-- **Strategy nesting.** With a proper backup, the column route is taken with
probability 1 when the problem is not recognized, and `(1 - R_y)^n` when it
is recognized as `y`, with `R_y` the chance that a search of `y`'s
associations clears the criterion. -/
theorem columns_prob (x : Problem) (hb : mass (backup x) = 1)
    (hT : ∀ y, total as (str y) ≠ 0) :
    prob (trial E N str as cc n backup x) isColumns =
      match N.select (E.code x) with
      | none => 1
      | some y => (1 - reach as (str y) cc) ^ n := by
  unfold trial
  cases h : N.select (E.code x) with
  | none =>
    simp only
    rw [prob_backup_part]
    simpa [isColumns, mass] using hb
  | some y =>
    simp only
    rw [prob_bind_split _ _ _ (fun _ => false) Retrieval.isExhausted 1]
    · rw [prob_false, prob_exhausted as (str y) cc (hT y)]; grind
    · intro r
      cases r with
      | stated a k => simp [prob_pure, isColumns, Retrieval.isExhausted]; grind
      | exhausted =>
        simp only [Retrieval.isExhausted]
        rw [prob_backup_part]
        simp only [isColumns, Route.columns_beq_columns, mass] at hb ⊢
        rw [hb]; grind

/-- **Whole-problem retrieval depends only on the route.** If `x` is recognized
as `y`, whole-problem retrieval on `x` states an answer with property `P`
exactly as often as retrieval on `y`'s associations does. -/
theorem whole_depends_only_on_route (x : Problem) (y : Item) (P : Nat → Bool)
    (h : N.select (E.code x) = some y) :
    prob (trial E N str as cc n backup x) (wholeSuch P) =
      prob (search as (str y) cc 0 n) (Retrieval.statedSuch P) := by
  unfold trial
  rw [h]
  simp only
  rw [prob_bind_split _ _ _ (Retrieval.statedSuch P) (fun _ => false) 0]
  · rw [prob_false]; grind
  · intro r
    cases r with
    | stated a k =>
      by_cases hp : P a <;> simp [prob_pure, wholeSuch, Retrieval.statedSuch, hp] <;> grind
    | exhausted =>
      simp only [Retrieval.statedSuch]
      rw [prob_backup_part]
      simp only [wholeSuch, Route.columns_beq_whole, Bool.false_and]
      rw [prob_false]; grind

/-- Two problems recognized as the same stored problem are answered alike by
whole-problem retrieval. -/
theorem same_route_same_retrieval (x x' : Problem) (y : Item) (P : Nat → Bool)
    (h : N.select (E.code x) = some y) (h' : N.select (E.code x') = some y) :
    prob (trial E N str as cc n backup x) (wholeSuch P) =
      prob (trial E N str as cc n backup x') (wholeSuch P) := by
  rw [whole_depends_only_on_route E N str as cc n backup x y P h,
    whole_depends_only_on_route E N str as cc n backup x' y P h']

/-- The stored problem `q`'s associations are *sharp* at criterion `cc`: no
answer but `q`'s sum clears it. -/
def Sharp (str : Item → Nat → Rat) (cc : Rat) (y : Item) (q : Problem) : Prop :=
  ∀ a, above (str y) cc a = true → a = q.sum

theorem isWhole_eq : isWhole = wholeSuch (fun _ => true) := by
  funext o; simp [isWhole, wholeSuch]

/-- **A confused problem gets its neighbour's answer.** If `x` is recognized as
the stored `code q`, and `q`'s associations are sharp, then every answer
whole-problem retrieval gives to `x` is `q`'s sum: answers other than `q`'s
sum have probability 0. -/
theorem confusion_gives_neighbours_answer (x q : Problem) (hT : total as (str (E.code q)) ≠ 0)
    (h : N.select (E.code x) = some (E.code q)) (hs : Sharp str cc (E.code q) q) :
    prob (trial E N str as cc n backup x) (wholeSuch fun a => a != q.sum) = 0 := by
  rw [whole_depends_only_on_route E N str as cc n backup x _ _ h, prob_stated _ _ _ _ hT]
  have : reachSuch as (str (E.code q)) cc (fun a => a != q.sum) = 0 := by
    simp only [reachSuch]
    rw [prob_congr _ _ (fun _ => false), prob_false]
    intro a
    by_cases ha : above (str (E.code q)) cc a
    · simp [hs a ha]
    · simp [ha]
  rw [this]; grind

/-- Retrieval on a sharp stored problem states a wrong answer for `x` exactly
as often as it states any answer, when `x`'s sum is not `q`'s. -/
theorem wrong_eq_whole_of_sharp (x q : Problem) (y : Item) (hT : total as (str y) ≠ 0)
    (h : N.select (E.code x) = some y) (hs : Sharp str cc y q) (hne : x.sum ≠ q.sum) :
    prob (trial E N str as cc n backup x) (wholeWrong x) =
      prob (trial E N str as cc n backup x) isWhole := by
  rw [wholeWrong, isWhole_eq, whole_depends_only_on_route E N str as cc n backup x y _ h,
    whole_depends_only_on_route E N str as cc n backup x y _ h,
    prob_stated _ _ _ _ hT, prob_stated _ _ _ _ hT]
  congr 1
  simp only [reachSuch]
  apply prob_congr
  intro a
  by_cases ha : above (str y) cc a
  · have := hs a ha
    simp [this, Ne.symm hne]
  · simp [ha]

/-- **Confident errors.** Let `q` be a stored problem that the net
recognizes, with sharp associations, and let `x` (with a different sum) be
confused with it. Then:

* on `q` itself, whole-problem retrieval never errs;
* on `x`, every whole-problem retrieval is an error;
* yet `x` falls back on the columns exactly as rarely as `q` does.

In DOA alone, a problem's retrieval errors and its backup use both come from
its own distribution, and go together. Confusion gives a problem another
problem's distribution, with its low backup use, and all of its errors. -/
theorem confident_errors (x q : Problem) (hT : ∀ y, total as (str y) ≠ 0)
    (hbx : mass (backup x) = 1) (hbq : mass (backup q) = 1)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hs : Sharp str cc (E.code q) q) (hne : x.sum ≠ q.sum) :
    prob (trial E N str as cc n backup q) (wholeWrong q) = 0 ∧
      prob (trial E N str as cc n backup x) (wholeWrong x) =
        prob (trial E N str as cc n backup x) isWhole ∧
      prob (trial E N str as cc n backup x) isColumns =
        prob (trial E N str as cc n backup q) isColumns := by
  refine ⟨confusion_gives_neighbours_answer E N str as cc n backup q q (hT _) hq hs,
    wrong_eq_whole_of_sharp E N str as cc n backup x q _ (hT _) hx hs hne, ?_⟩
  rw [columns_prob E N str as cc n backup x hbx hT, columns_prob E N str as cc n backup q hbq hT,
    hx, hq]

/-- **Confusion with a problem of the same sum is harmless.** If `x` is
recognized as the stored `code q`, which the net recognizes as itself, and
the two sums agree, then whole-problem retrieval errs on `x` exactly as
often as on `q`. -/
theorem same_sum_confusion_harmless (x q : Problem)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hsum : x.sum = q.sum) :
    prob (trial E N str as cc n backup x) (wholeWrong x) =
      prob (trial E N str as cc n backup q) (wholeWrong q) := by
  rw [wholeWrong, wholeWrong, hsum]
  exact same_route_same_retrieval E N str as cc n backup x q _ _ hx hq

/-- **Commuted confusions are harmless**: confusing `a + b` with `b + a`. -/
theorem commuted_confusion_harmless (x : Problem)
    (hq : N.select (E.code x.swap) = some (E.code x.swap))
    (hx : N.select (E.code x) = some (E.code x.swap)) :
    prob (trial E N str as cc n backup x) (wholeWrong x) =
      prob (trial E N str as cc n backup x.swap) (wholeWrong x.swap) :=
  same_sum_confusion_harmless E N str as cc n backup x x.swap hq hx
    (by simp [Problem.sum, Problem.swap, Nat.add_comm])

/-- A confused problem has the same digits as its neighbour wherever its path
tests all of a digit's features. -/
theorem confused_digit (x q : Problem) (i : Addend) (j : Place) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ f ∈ E.features i j, f ∈ N.path (E.code x)) :
    x.digit i j = q.digit i j :=
  Net.confusion_preserves N E.code _ (fun p => p.digit i j) (fun p q => E.determines p q i j)
    x q hnd hq hx hcover

/-- **Near misses: within 200.** If each image is stored once, `x` is confused
with `q`, and `x`'s path tests the hundreds digits of both addends, then the
answer `x` gets by confusion (`q`'s sum) is within 200 of the right one. -/
theorem near_miss_200 (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ i, ∀ f ∈ E.features i .hundreds, f ∈ N.path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 200 ∧ x.sum < q.sum + 200 := by
  have h1 := confused_digit E N x q .first .hundreds hnd hq hx (hcover .first)
  have h2 := confused_digit E N x q .second .hundreds hnd hq hx (hcover .second)
  simp only [Problem.digit, Problem.addend, digitOf] at h1 h2
  simp only [Problem.sum]
  omega

/-- **Near misses: within 20**, when the path also tests the tens digits. -/
theorem near_miss_20 (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ i, ∀ j, j ≠ Place.units → ∀ f ∈ E.features i j, f ∈ N.path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 20 ∧ x.sum < q.sum + 20 := by
  have h1 := confused_digit E N x q .first .hundreds hnd hq hx (hcover .first _ (by decide))
  have h2 := confused_digit E N x q .second .hundreds hnd hq hx (hcover .second _ (by decide))
  have h3 := confused_digit E N x q .first .tens hnd hq hx (hcover .first _ (by decide))
  have h4 := confused_digit E N x q .second .tens hnd hq hx (hcover .second _ (by decide))
  simp only [Problem.digit, Problem.addend, digitOf] at h1 h2 h3 h4
  simp only [Problem.sum]
  omega

/-- **Practiced problems stay practiced.** Learning a new problem (EPAM F1)
never changes how a studied problem is answered: its whole trial is the
same before and after. -/
theorem learning_preserves_trial (order : NoticingOrder) (q : Problem) (z : Item)
    (hq : Net.Recognizes N (E.code q)) (hz : E.code q ≠ z) :
    trial E (N.learn order z) str as cc n backup q = trial E N str as cc n backup q := by
  have h' : Net.Recognizes (N.learn order z) (E.code q) := Net.learn_preserves order N z _ hq hz
  unfold trial
  unfold Net.Recognizes at hq h'
  rw [hq, h']

/-- **Similar problems take longer to recognize.** Codes that agree on the
first `k` features of the noticing order cost at least `k` scanning steps to
tell apart (EPAM). -/
theorem similar_problems_cost_time (order : NoticingOrder) (x q : Problem) (k : Nat)
    (hk : k ≤ order.length) (h : ∀ f ∈ order.take k, (E.code x).feat f = (E.code q).feat f) :
    k ≤ scanCost order (E.code x) (E.code q) :=
  scanCost_ge_of_agree order _ _ k hk h

end MD
