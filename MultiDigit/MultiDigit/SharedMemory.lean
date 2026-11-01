/-
The integrated multi-digit model with one memory for whole problems and
column facts.

In `Integrated.lean` the column solver adds each column by a single-digit DOA
trial whose associations are a separate table (`Facts.s`). Here a column's
addition goes through the same memory as whole-problem recall:
1. the digit pair `d + e` is coded in the problems' own code space, as the
   problem `d + e` (both digits in the units column, `pairCode`);
2. the memory (any `retrieve`, the same one that recognizes whole problems)
   calls up a stored code, and retrieval searches *its* associations, in the
   same strength table `str` as whole problems;
3. when nothing is called up, or retrieval is exhausted, DOA's backup puts up
   fingers and counts (`colBackup`). The backup works on the pair as
   presented: its elaboration uses the pair's own associations, not those of
   whatever was called up. This is a stated choice.

A column fact is `recognizeRetrieve` on digit pairs (`memFact`), so the
solver, which is parametric in its facts, needs no change, and
`Solver.bridge` still makes it the column procedure.

What each result rests on:

| Kind | Results |
|---|---|
| **Consequence of the composition** (every memory, encoding, strength table and DOA parameter set) | `sharedBackup_eq_columns`; `memFact_self` (with each pair recognized as itself, a column fact *is* the DOA fact on the pair's associations); `sharedBackup_reduces`, `strial_reduces`, `strial_net_reduces` (so the shared model is the integrated model of `Integrated.lean`, and inherits its theorems); `mass_colBackup`, `same_memFastFact` |
| **Conditional**, given the conditions named in its docstring | `column_confident_errors` (a digit pair confused with another, sharp associations: the confusion-error pattern at the column level); `confused_column_gives_neighbours_sum` |
| **The illustrative setting** (chosen numbers) | `setting_*`: EPAM's net learns the three digit pairs and the two problems, and the shared model gives the integrated model's values; ACT-R's memory, studying the same five, does not: column facts and whole problems compete for retrieval |

The memory here is stateless during a trial: retrieval does not change it.
ACT-R's retrieval as use is open (OPEN_ISSUES #24, stage 2).
-/

import MultiDigit.Integrated

namespace MD.Shared

open Cog Dist MD

/-- A digit pair as a problem: `d + e`, both digits in the units column. -/
def pair (d e : Nat) : Problem := ⟨d, e⟩

/-- A digit pair's code, in the problems' code space. -/
def pairCode (E : Encoding) (pr : Nat × Nat) : Item := E.code (pair pr.1 pr.2)

/-- **The column backup** (DOA, A4 and A5): put up fingers and retrieve once
more from the pair's elaborated associations; if that fails, count. -/
def colBackup (E : Encoding) (str : Item → Nat → Rat) (as : List Nat) (bk : SC.Backup) (cc : Rat)
    (pr : Nat × Nat) : Dist Nat :=
  Dist.bind (SC.backup as (str (pairCode E pr)) bk cc ⟨pr.1, pr.2⟩) fun o => Dist.pure o.2

/-- **A column fact from the shared memory**: recognize the digit pair,
retrieve on what is called up, else back up. -/
def memFact (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
    (as : List Nat) (bk : SC.Backup) (cc : Rat) (n : Nat) (d e : Nat) : Dist Nat :=
  Dist.bind (recognizeRetrieve (pairCode E) retrieve str as cc n (colBackup E str as bk cc) (d, e))
    fun o => Dist.pure o.2

/-- **The solver with shared-memory facts.** -/
def sharedBackup (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
    (cas : List Nat) (bk : SC.Backup) (ccc : Rat) (cn : Nat) (p : Problem) : Dist Nat :=
  Solver.answers (memFact retrieve E str cas bk ccc cn) Solver.full Solver.lenient p

/-- **A trial with one memory**: the memory `retrieve` and the strengths `str`
serve both whole-problem recall and the solver's column facts. The answer
sets, criteria and search lengths of the two levels are separate
(`as`, `cc`, `n` for whole problems; `cas`, `ccc`, `cn` for columns). -/
def strial (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
    (as : List Nat) (cc : Rat) (n : Nat) (cas : List Nat) (bk : SC.Backup) (ccc : Rat) (cn : Nat)
    (x : Problem) : Dist (Route × Nat) :=
  trialWith retrieve E str as cc n (sharedBackup retrieve E str cas bk ccc cn) x

/-- The DOA parameters the shared memory amounts to when each pair is
recognized as itself: the pair's associations, read from `str`. -/
def pairFacts (E : Encoding) (str : Item → Nat → Rat) (cas : List Nat) (bk : SC.Backup) (ccc : Rat)
    (cn : Nat) : Integrated.Facts :=
  ⟨cas, fun p => str (E.code (pair p.a p.b)), bk, ccc, cn⟩

/-! ### Consequences of the composition -/

theorem sharedBackup_eq_columns (retrieve : Item → Dist (Option Item)) (E : Encoding)
    (str : Item → Nat → Rat) (cas : List Nat) (bk : SC.Backup) (ccc : Rat) (cn : Nat) (p : Problem) :
    sharedBackup retrieve E str cas bk ccc cn p = columns (memFact retrieve E str cas bk ccc cn) p :=
  Solver.bridge _ p

/-- **With a pair recognized as itself, the column fact is the DOA fact** on
the pair's own associations. So the separate table of `Integrated.lean` is
the special case of a memory that recognizes every digit pair it is asked. -/
theorem memFact_self (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
    (as : List Nat) (bk : SC.Backup) (cc : Rat) (n d e : Nat)
    (h : retrieve (pairCode E (d, e)) = Dist.pure (some (pairCode E (d, e)))) :
    memFact retrieve E str as bk cc n d e = (pairFacts E str as bk cc n).fact d e := by
  unfold memFact
  rw [RR.recognizeRetrieve_certain _ _ _ _ _ _ _ _ _ h]
  simp only [RR.afterRecognition, Integrated.Facts.fact, pairFacts, doaFact, SC.trial, bind_assoc]
  congr 1
  funext r
  cases r with
  | stated a k => simp only [bind_pure_left]
  | exhausted =>
    simp only [colBackup, bind_assoc, bind_pure_left]
    rfl

/-- If the memory recognizes the digit pairs of `p`'s three columns as
themselves, the shared solver is the integrated model's solver. -/
theorem sharedBackup_reduces (retrieve : Item → Dist (Option Item)) (E : Encoding)
    (str : Item → Nat → Rat) (cas : List Nat) (bk : SC.Backup) (ccc : Rat) (cn : Nat) (p : Problem)
    (h : ∀ j, retrieve (pairCode E (p.digit .first j, p.digit .second j)) =
      Dist.pure (some (pairCode E (p.digit .first j, p.digit .second j)))) :
    sharedBackup retrieve E str cas bk ccc cn p =
      Integrated.solverBackup (pairFacts E str cas bk ccc cn) p := by
  rw [sharedBackup_eq_columns, Integrated.solverBackup_eq_columns]
  unfold columns
  rw [memFact_self _ _ _ _ _ _ _ _ _ (h .units), memFact_self _ _ _ _ _ _ _ _ _ (h .tens),
    memFact_self _ _ _ _ _ _ _ _ _ (h .hundreds)]

/-- **The shared model reduces to the integrated model** when `x`'s digit
pairs are recognized as themselves: the same distribution, so every theorem
of `Integrated.lean` holds of it. -/
theorem strial_reduces (retrieve : Item → Dist (Option Item)) (E : Encoding)
    (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat) (cas : List Nat) (bk : SC.Backup)
    (ccc : Rat) (cn : Nat) (x : Problem)
    (h : ∀ j, retrieve (pairCode E (x.digit .first j, x.digit .second j)) =
      Dist.pure (some (pairCode E (x.digit .first j, x.digit .second j)))) :
    strial retrieve E str as cc n cas bk ccc cn x =
      trialWith retrieve E str as cc n (Integrated.solverBackup (pairFacts E str cas bk ccc cn)) x := by
  have hb := sharedBackup_reduces retrieve E str cas bk ccc cn x h
  unfold strial trialWith
  congr 1
  funext r
  cases r <;> simp only [afterRetrieval, hb]

/-- The same for a discrimination net: the shared trial is `Integrated.itrial`. -/
theorem strial_net_reduces (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat)
    (cc : Rat) (n : Nat) (cas : List Nat) (bk : SC.Backup) (ccc : Rat) (cn : Nat) (x : Problem)
    (h : ∀ j, N.select (pairCode E (x.digit .first j, x.digit .second j)) =
      some (pairCode E (x.digit .first j, x.digit .second j))) :
    strial N.retrieve E str as cc n cas bk ccc cn x =
      Integrated.itrial E N str as cc n (pairFacts E str cas bk ccc cn) x := by
  rw [strial_reduces _ _ _ _ _ _ _ _ _ _ x fun j => N.retrieve_of_select _ _ (h j),
    Integrated.itrial, trial_eq_trialWith]

/-- The column backup is proper when the pair's elaborated associations have
positive total. -/
theorem mass_colBackup (E : Encoding) (str : Item → Nat → Rat) (as : List Nat) (bk : SC.Backup)
    (cc : Rat) (pr : Nat × Nat)
    (hE : total as (SC.elaborate (str (pairCode E pr)) (pr.1 + pr.2) bk.e) ≠ 0) :
    mass (colBackup E str as bk cc pr) = 1 := by
  unfold colBackup SC.backup
  apply mass_bind _ _ _ fun _ => mass_pure _
  apply mass_bind _ _ (mass_sample _ _ hE)
  intro a
  split
  · exact mass_pure _
  · exact mass_bind _ _ (SC.mass_count _ _ _) fun _ => mass_pure _

/-! ### Conditional results -/

/-- **Confident errors at the column level.** Given that the memory
recognizes the digit pair `(d', e')` as itself and takes `(d, e)` for it,
that `(d', e')`'s associations are sharp, that the sums differ, and that the
backups are proper: retrieval never errs on `(d', e')`, every retrieved
answer to `(d, e)` is wrong, and `(d, e)` falls back on fingers and counting
exactly as often as `(d', e')`. `RR.confident_errors`, on digit pairs. -/
theorem column_confident_errors (retrieve : Item → Dist (Option Item)) (E : Encoding)
    (str : Item → Nat → Rat) (as : List Nat) (bk : SC.Backup) (cc : Rat) (n : Nat)
    (d e d' e' : Nat) (hT : ∀ y, total as (str y) ≠ 0)
    (hb : ∀ pr, mass (colBackup E str as bk cc pr) = 1)
    (hq : retrieve (pairCode E (d', e')) = Dist.pure (some (pairCode E (d', e'))))
    (hx : retrieve (pairCode E (d, e)) = Dist.pure (some (pairCode E (d', e'))))
    (hs : RR.Sharp str cc (pairCode E (d', e')) (d' + e')) (hne : d + e ≠ d' + e') :
    Phenomena.ConfusionErrorPattern
      (recognizeRetrieve (pairCode E) retrieve str as cc n (colBackup E str as bk cc))
      (RR.wholeWrong fun pr : Nat × Nat => pr.1 + pr.2) RR.isWhole RR.isBackup (d, e) (d', e') :=
  RR.confident_errors (pairCode E) retrieve str as cc n (colBackup E str as bk cc)
    (fun pr : Nat × Nat => pr.1 + pr.2) (d, e) (d', e') hT (hb _) (hb _) hq hx hs hne

/-- **A confused column retrieves the confusing pair's sum.** Given that
`(d, e)` is taken for `(d', e')` for certain, with sharp associations, the
column fact is never a retrieved answer other than `d' + e'`: whatever else
it gives comes from fingers and counting on `(d, e)` itself. -/
theorem confused_column_gives_neighbours_sum (retrieve : Item → Dist (Option Item)) (E : Encoding)
    (str : Item → Nat → Rat) (as : List Nat) (bk : SC.Backup) (cc : Rat) (n : Nat)
    (d e d' e' : Nat) (hT : total as (str (pairCode E (d', e'))) ≠ 0)
    (hx : retrieve (pairCode E (d, e)) = Dist.pure (some (pairCode E (d', e'))))
    (hs : RR.Sharp str cc (pairCode E (d', e')) (d' + e')) :
    prob (recognizeRetrieve (pairCode E) retrieve str as cc n (colBackup E str as bk cc) (d, e))
      (RR.wholeWrong (fun _ : Nat × Nat => d' + e') (d, e)) = 0 :=
  RR.confusion_gives_neighbours_answer (pairCode E) retrieve str as cc n (colBackup E str as bk cc)
    (fun _ : Nat × Nat => d' + e') (d, e) (d', e') hT hx hs

/-! ### Exact evaluation -/

/-- The column backup, merged. -/
def colBackupFast (E : Encoding) (str : Item → Nat → Rat) (as : List Nat) (bk : SC.Backup) (cc : Rat)
    (pr : Nat × Nat) : Dist Nat :=
  merge (Dist.bind (SC.backupMerged as (str (pairCode E pr)) bk cc ⟨pr.1, pr.2⟩) fun o => Dist.pure o.2)

theorem same_colBackupFast (E : Encoding) (str : Item → Nat → Rat) (as : List Nat) (bk : SC.Backup)
    (cc : Rat) (pr : Nat × Nat) : Same (colBackupFast E str as bk cc pr) (colBackup E str as bk cc pr) := by
  intro h
  rw [colBackupFast, same_merge]
  exact same_bind (SC.same_backupMerged _ _ _ _ _) (fun _ => Same.refl _) h

/-- Recognize-retrieve depends on its backup only as a distribution. -/
theorem same_recognizeRetrieve {P A : Type} (code : P → Item) (retrieve : Item → Dist (Option Item))
    (str : Item → A → Rat) (as : List A) (cc : Rat) (n : Nat) (b b' : P → Dist A) (x : P)
    (hb : Same (b x) (b' x)) :
    Same (recognizeRetrieve code retrieve str as cc n b x) (recognizeRetrieve code retrieve str as cc n b' x) := by
  have hk : Same (Dist.bind (b x) fun r => Dist.pure (Route.backup, r))
      (Dist.bind (b' x) fun r => Dist.pure (Route.backup, r)) :=
    same_bind hb fun _ => Same.refl _
  unfold recognizeRetrieve
  refine same_bind (Same.refl _) fun r => ?_
  cases r with
  | none => exact hk
  | some y =>
    exact same_bind (Same.refl _) fun o => by cases o <;> first | exact Same.refl _ | exact hk

/-- A shared-memory column fact, merged. -/
def memFastFact (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
    (as : List Nat) (bk : SC.Backup) (cc : Rat) (n : Nat) (d e : Nat) : Dist Nat :=
  merge (Dist.bind (recognizeRetrieve (pairCode E) retrieve str as cc n (colBackupFast E str as bk cc) (d, e))
    fun o => Dist.pure o.2)

theorem same_memFastFact (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
    (as : List Nat) (bk : SC.Backup) (cc : Rat) (n d e : Nat) :
    Same (memFastFact retrieve E str as bk cc n d e) (memFact retrieve E str as bk cc n d e) := by
  intro h
  rw [memFastFact, same_merge]
  exact same_bind (same_recognizeRetrieve _ _ _ _ _ _ _ _ _ (same_colBackupFast E str as bk cc _))
    (fun _ => Same.refl _) h

/-- The shared solver, merged. -/
def sharedFast (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
    (cas : List Nat) (bk : SC.Backup) (ccc : Rat) (cn : Nat) (p : Problem) : Dist Nat :=
  merge (columns (memFastFact retrieve E str cas bk ccc cn) p)

theorem same_sharedFast (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
    (cas : List Nat) (bk : SC.Backup) (ccc : Rat) (cn : Nat) (p : Problem) :
    Same (sharedFast retrieve E str cas bk ccc cn p) (sharedBackup retrieve E str cas bk ccc cn p) := by
  intro h
  rw [sharedFast, same_merge, sharedBackup_eq_columns]
  exact same_bind (same_memFastFact _ _ _ _ _ _ _ _ _) (fun _ =>
    same_bind (same_memFastFact _ _ _ _ _ _ _ _ _) fun _ =>
      same_bind (same_memFastFact _ _ _ _ _ _ _ _ _) fun _ => Same.refl _) h

theorem prob_strial_fast (retrieve : Item → Dist (Option Item)) (E : Encoding)
    (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat) (cas : List Nat) (bk : SC.Backup)
    (ccc : Rat) (cn : Nat) (x : Problem) (e : Route × Nat → Bool) :
    prob (strial retrieve E str as cc n cas bk ccc cn x) e =
      prob (trialWith retrieve E str as cc n (sharedFast retrieve E str cas bk ccc cn) x) e :=
  Integrated.prob_trialWith_same retrieve E str as cc n _ _ x
    (fun h => (same_sharedFast retrieve E str cas bk ccc cn x h).symm) e

/-- `columns` uses its facts only at the problem's three digit pairs. -/
theorem columns_congr (f g : Nat → Nat → Dist Nat) (p : Problem)
    (h : ∀ j, f (p.digit .first j) (p.digit .second j) = g (p.digit .first j) (p.digit .second j)) :
    columns f p = columns g p := by
  unfold columns
  rw [h .units, h .tens, h .hundreds]

/-- A trial's probabilities, with the shared solver's facts at `x`'s three
digit pairs replaced by given distributions `f` (certified once each). -/
theorem prob_strial_tab (retrieve : Item → Dist (Option Item)) (E : Encoding)
    (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat) (cas : List Nat) (bk : SC.Backup)
    (ccc : Rat) (cn : Nat) (f : Nat → Nat → Dist Nat) (x : Problem)
    (h : ∀ j, memFastFact retrieve E str cas bk ccc cn (x.digit .first j) (x.digit .second j) =
      f (x.digit .first j) (x.digit .second j)) (e : Route × Nat → Bool) :
    prob (strial retrieve E str as cc n cas bk ccc cn x) e =
      prob (trialWith retrieve E str as cc n (fun p => merge (columns f p)) x) e := by
  apply Integrated.prob_trialWith_same retrieve E str as cc n _ _ x
  intro k
  rw [← same_sharedFast retrieve E str cas bk ccc cn x k, sharedFast, columns_congr _ _ x h]

/-! ### The illustrative setting

The setting of `Integrated.lean` (encoding, whole-problem strengths, the
single-digit rule `colStr`, the DOA parameters of `F0`), with one memory.
The memory studies the three digit pairs that 150 + 100 and 100 + 100 need
(0 + 0, 5 + 0, 1 + 1), then the two problems. -/

open Example Integrated

/-- One strength table: the digit pairs' associations by `colStr`, the
problems' as in `Example`. -/
def sstr (y : Item) (a : Nat) : Rat :=
  if y = pairCode bcd (0, 0) then colStr ⟨0, 0⟩ a
  else if y = pairCode bcd (5, 0) then colStr ⟨5, 0⟩ a
  else if y = pairCode bcd (1, 1) then colStr ⟨1, 1⟩ a
  else Example.str y a

/-- What is studied, in order: the digit pairs, then the problems. -/
def studied : List Item :=
  [pairCode bcd (0, 0), pairCode bcd (5, 0), pairCode bcd (1, 1), bcd.code q1, bcd.code q2]

/-- EPAM's net after learning them. -/
def snet : Net := studied.foldl (fun N c => N.learn order c) (Net.leaf none)

/-- ACT-R's memory after studying them (the parameters of `ExampleACTR`). -/
def smem : ActState := studied.foldl Act.study ⟨0, []⟩

/-- ACT-R's retrieval from that memory. -/
abbrev sact : Item → Dist (Option Item) := (actRetriever ExampleACTR.P).retrieve smem

/-- A trial in the setting, with memory `r`. -/
abbrev sit (r : Item → Dist (Option Item)) (p : Problem) : Dist (Route × Nat) :=
  strial r bcd sstr answers (1 / 2) 1 F0.as F0.bk F0.cc F0.n p

/-- The net recognizes all five as themselves, and takes 150 + 100 for
100 + 100. -/
theorem setting_net_facts :
    studied.all (fun c => snet.select c == some c) ∧ snet.select (bcd.code x) = some (bcd.code q1) := by
  decide +kernel

/-- **With EPAM's net, the shared model is the integrated model** on
150 + 100 (`strial_net_reduces`): the net recognizes each column's digit
pair as itself. -/
theorem setting_epam_reduces :
    sit snet.retrieve x = itrial bcd snet sstr answers (1 / 2) 1 (pairFacts bcd sstr F0.as F0.bk F0.cc F0.n) x ∧
      sit snet.retrieve q1 =
        itrial bcd snet sstr answers (1 / 2) 1 (pairFacts bcd sstr F0.as F0.bk F0.cc F0.n) q1 :=
  ⟨strial_net_reduces _ _ _ _ _ _ _ _ _ _ x (by intro j; cases j <;> decide +kernel),
    strial_net_reduces _ _ _ _ _ _ _ _ _ _ q1 (by intro j; cases j <;> decide +kernel)⟩

/-- **The same values as `Integrated.lean`**: 150 + 100 answered 200 with
probability about .978 and 250 about .014; 100 + 100 answered correctly
about .993. One memory changes nothing for EPAM. -/
theorem setting_epam_values :
    prob (sit snet.retrieve x) (fun o => o.2 == 200) = 1821856162746747614607 / 1862341855000000000000 ∧
      prob (sit snet.retrieve x) (fun o => o.2 == 250) = 4991328328911197 / 349801250000000000 ∧
      prob (sit snet.retrieve q1) (fun o => o.2 == 200) = 868108399577 / 874503125000 := by
  rw [setting_epam_reduces.1, setting_epam_reduces.2]
  simp only [prob_itrial_fast]
  decide +kernel

/-- ACT-R's column fact for 0 + 0 in the setting. -/
def act00 : Dist Nat :=
  [(1, 117324/1246025), (0, 943551/1246025), (3, 24/2167), (2, 160/2167), (6, 18/2167), (5, 120/2167)]

/-- ACT-R's column fact for 5 + 0. -/
def act50 : Dist Nat :=
  [(0, 176640060939/2803240000000), (1, 2650148451/280324000000), (2, 58919549411/560648000000),
    (3, 108490683/6371000000), (4, 11761227/1012000000), (7, 89397513/70081000000),
    (8, 3595401/50968000000), (9, 548451/280324000000), (10, 60939/2803240000000),
    (6, 2682379989/25484000000), (5, 481586304093/700810000000)]

/-- ACT-R's column fact for 1 + 1. -/
def act11 : Dist Nat :=
  [(4, 63369/388355000), (0, 22143369/388355000), (1, 1398321/97088750), (3, 10314921/97088750),
    (2, 143777647/194177500), (6, 36/3377), (5, 240/3377)]

/-- The three, as a table. -/
def actTab (d e : Nat) : Dist Nat := if d = 0 ∧ e = 0 then act00 else if d = 5 ∧ e = 0 then act50 else act11

theorem act_tab_x (j : Place) :
    memFastFact sact bcd sstr F0.as F0.bk F0.cc F0.n (x.digit .first j) (x.digit .second j) =
      actTab (x.digit .first j) (x.digit .second j) := by
  cases j <;> decide +kernel

theorem act_tab_q1 (j : Place) :
    memFastFact sact bcd sstr F0.as F0.bk F0.cc F0.n (q1.digit .first j) (q1.digit .second j) =
      actTab (q1.digit .first j) (q1.digit .second j) := by
  cases j <;> decide +kernel

/-- **Digit pairs are confused with each other under ACT-R.** The code of 0 + 0
calls up itself with probability 48/197 and 5 + 0 with 15/197; so 0 + 0 is
answered 5 (5 + 0's sum, retrieved) with probability 120/2167. 150 + 100
calls up a digit pair with probability 83/1187. EPAM's net calls up each
pair, and each problem, as itself (`setting_net_facts`). -/
theorem setting_act_pairs :
    prob (sact (pairCode bcd (0, 0))) (· == some (pairCode bcd (0, 0))) = 48 / 197 ∧
      prob (sact (pairCode bcd (0, 0))) (· == some (pairCode bcd (5, 0))) = 15 / 197 ∧
      prob (memFact sact bcd sstr F0.as F0.bk F0.cc F0.n 0 0) (· == 5) = 120 / 2167 ∧
      prob (sact (bcd.code x)) (fun r => r == some (pairCode bcd (0, 0)) ||
        r == some (pairCode bcd (5, 0)) || r == some (pairCode bcd (1, 1))) = 83 / 1187 := by
  rw [← (same_memFastFact sact bcd sstr F0.as F0.bk F0.cc F0.n 0 0).prob]
  decide +kernel

set_option maxRecDepth 100000 in
/-- **With ACT-R's memory, sharing hurts.** Compare `Integrated.setting_actr_x`
and `setting_practiced_errors`, where ACT-R holds only the two problems and
the columns use DOA's separate table:
* 150 + 100 is answered 200 by retrieval with probability 10800/27301
  (about .396, against .425), and reaches the solver with 11101/27301 (about
  .407, against .362);
* the solver gets 150 + 100 right with probability about .385 (against .656),
  so it is answered 250 overall with about .157 (against .238);
* the practiced 100 + 100 is answered wrongly with about .386 (against .334).
Whole problems and digit pairs compete for retrieval in one memory. This is
ACT-R's retrieval rule without retrieval as use: memory changes only by study,
not by the retrievals of the trial, so these values will change when that is
added (OPEN_ISSUES #24, stage 2). -/
theorem setting_act_values :
    prob (sit sact x) (wholeSuch (· == 200)) = 10800 / 27301 ∧
      prob (sit sact x) isColumns = 11101 / 27301 ∧
      prob (sharedBackup sact bcd sstr F0.as F0.bk F0.cc F0.n x) (· == 250) =
        65332740910454767471306221 / 169560993121994375000000000 ∧
      prob (sit sact x) (fun o => o.2 == 250) =
        725258756846958373698970359321 / 4629184673223568431875000000000 ∧
      prob (sit sact q1) (fun o => o.2 != 200) =
        19872761679504584480161 / 51517475683410292187500 := by
  rw [← (same_sharedFast sact bcd sstr F0.as F0.bk F0.cc F0.n x).prob, sharedFast,
    columns_congr _ _ x act_tab_x]
  simp only [sit, prob_strial_tab _ _ _ _ _ _ _ _ _ _ _ x act_tab_x,
    prob_strial_tab _ _ _ _ _ _ _ _ _ _ _ q1 act_tab_q1]
  decide +kernel

end MD.Shared
