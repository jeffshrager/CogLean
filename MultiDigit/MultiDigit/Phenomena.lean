/-
What the combined model predicts, deduced from its postulates.

Every theorem holds for any encoding, net, strengths, criterion, search
length and backup. Each is the theorem of the same name in `AnyMemory.lean`,
which holds for any memory, applied to a discrimination net's retrieval
(`trial_eq_trialWith`). Where the general theorem needs a law of memory, the
net supplies it: `net_agreesOn` (a confusion agrees on the features its path
tests) and `netRetriever_stableRetrieval` (learning is local).

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

import MultiDigit.AnyMemory

namespace MD

open Cog Dist

variable (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat)
  (backup : Problem → Dist Nat)

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
  rw [trial_eq_trialWith]
  cases h : N.select (E.code x) <;>
    exact AnyMemory.columns_prob_certain N.retrieve E str as cc n backup x _
      (N.retrieve_of_select _ _ h) hb hT

/-- **Whole-problem retrieval depends only on the route.** If `x` is recognized
as `y`, whole-problem retrieval on `x` states an answer with property `P`
exactly as often as retrieval on `y`'s associations does. -/
theorem whole_depends_only_on_route (x : Problem) (y : Item) (P : Nat → Bool)
    (h : N.select (E.code x) = some y) :
    prob (trial E N str as cc n backup x) (wholeSuch P) =
      prob (search as (str y) cc 0 n) (Retrieval.statedSuch P) := by
  rw [trial_eq_trialWith]
  exact AnyMemory.whole_depends_only_on_route N.retrieve E str as cc n backup x y P
    (N.retrieve_of_select _ _ h)

/-- Two problems recognized as the same stored problem are answered alike by
whole-problem retrieval. -/
theorem same_route_same_retrieval (x x' : Problem) (y : Item) (P : Nat → Bool)
    (h : N.select (E.code x) = some y) (h' : N.select (E.code x') = some y) :
    prob (trial E N str as cc n backup x) (wholeSuch P) =
      prob (trial E N str as cc n backup x') (wholeSuch P) := by
  simp only [trial_eq_trialWith]
  exact AnyMemory.same_route_same_retrieval N.retrieve E str as cc n backup x x' y P
    (N.retrieve_of_select _ _ h) (N.retrieve_of_select _ _ h')

/-- **A confused problem gets its neighbour's answer.** If `x` is recognized as
the stored `code q`, and `q`'s associations are sharp, then every answer
whole-problem retrieval gives to `x` is `q`'s sum: answers other than `q`'s
sum have probability 0. -/
theorem confusion_gives_neighbours_answer (x q : Problem) (hT : total as (str (E.code q)) ≠ 0)
    (h : N.select (E.code x) = some (E.code q)) (hs : Sharp str cc (E.code q) q) :
    prob (trial E N str as cc n backup x) (wholeSuch fun a => a != q.sum) = 0 := by
  rw [trial_eq_trialWith]
  exact AnyMemory.confusion_gives_neighbours_answer N.retrieve E str as cc n backup x q hT
    (N.retrieve_of_select _ _ h) hs

/-- Retrieval on a sharp stored problem states a wrong answer for `x` exactly
as often as it states any answer, when `x`'s sum is not `q`'s. -/
theorem wrong_eq_whole_of_sharp (x q : Problem) (y : Item) (hT : total as (str y) ≠ 0)
    (h : N.select (E.code x) = some y) (hs : Sharp str cc y q) (hne : x.sum ≠ q.sum) :
    prob (trial E N str as cc n backup x) (wholeWrong x) =
      prob (trial E N str as cc n backup x) isWhole := by
  rw [trial_eq_trialWith]
  exact AnyMemory.wrong_eq_whole_of_sharp N.retrieve E str as cc n backup x q y hT
    (N.retrieve_of_select _ _ h) hs hne

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
  simp only [trial_eq_trialWith]
  exact AnyMemory.confident_errors N.retrieve E str as cc n backup x q hT hbx hbq
    (N.retrieve_of_select _ _ hq) (N.retrieve_of_select _ _ hx) hs hne

/-- **Confusion with a problem of the same sum is harmless.** If `x` is
recognized as the stored `code q`, which the net recognizes as itself, and
the two sums agree, then whole-problem retrieval errs on `x` exactly as
often as on `q`. -/
theorem same_sum_confusion_harmless (x q : Problem)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hsum : x.sum = q.sum) :
    prob (trial E N str as cc n backup x) (wholeWrong x) =
      prob (trial E N str as cc n backup q) (wholeWrong q) := by
  simp only [trial_eq_trialWith]
  exact AnyMemory.same_sum_confusion_harmless N.retrieve E str as cc n backup x q
    (N.retrieve_of_select _ _ hq) (N.retrieve_of_select _ _ hx) hsum

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
  AnyMemory.confused_digit N.retrieve E x q i j (net_agreesOn N _ _ _ hnd hq hx hcover)
    (N.possible_retrieve _ _ hx)

/-- **Near misses: within 200.** If each image is stored once, `x` is confused
with `q`, and `x`'s path tests the hundreds digits of both addends, then the
answer `x` gets by confusion (`q`'s sum) is within 200 of the right one. -/
theorem near_miss_200 (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ i, ∀ f ∈ E.features i .hundreds, f ∈ N.path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 200 ∧ x.sum < q.sum + 200 :=
  AnyMemory.near_miss_200 N.retrieve E x q (fun i => net_agreesOn N _ _ _ hnd hq hx (hcover i))
    (N.possible_retrieve _ _ hx) hxa hxb hqa hqb

/-- **Near misses: within 20**, when the path also tests the tens digits. -/
theorem near_miss_20 (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ i, ∀ j, j ≠ Place.units → ∀ f ∈ E.features i j, f ∈ N.path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 20 ∧ x.sum < q.sum + 20 :=
  AnyMemory.near_miss_20 N.retrieve E x q
    (fun i j hj => net_agreesOn N _ _ _ hnd hq hx (hcover i j hj))
    (N.possible_retrieve _ _ hx) hxa hxb hqa hqb

/-- **Practiced problems stay practiced.** Learning a new problem (EPAM F1)
never changes how a studied problem is answered: its whole trial is the
same before and after. -/
theorem learning_preserves_trial (order : NoticingOrder) (q : Problem) (z : Item)
    (hq : Net.Recognizes N (E.code q)) (hz : E.code q ≠ z) :
    trial E (N.learn order z) str as cc n backup q = trial E N str as cc n backup q := by
  simp only [trial_eq_trialWith]
  exact AnyMemory.learning_preserves_trial E str as cc n backup (netRetriever order)
    (netRetriever_stableRetrieval order) N q z (N.retrieve_of_select _ _ hq) hz

/-- **Similar problems take longer to recognize.** Codes that agree on the
first `k` features of the noticing order cost at least `k` scanning steps to
tell apart (EPAM). -/
theorem similar_problems_cost_time (order : NoticingOrder) (x q : Problem) (k : Nat)
    (hk : k ≤ order.length) (h : ∀ f ∈ order.take k, (E.code x).feat f = (E.code q).feat f) :
    k ≤ scanCost order (E.code x) (E.code q) :=
  scanCost_ge_of_agree order _ _ k hk h

end MD
