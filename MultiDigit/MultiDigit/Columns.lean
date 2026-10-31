/-
The column backup (M4), built from single-digit addition facts.

When a problem is not recognized, or whole-problem retrieval is exhausted,
the child adds column by column: units, then tens, then hundreds. Each
column's two digits are added by a single-digit process (`fact`). The
column's last digit is written down, and its tens are carried into the next
column. The single-digit process can be the distributions-of-associations
trial itself (`doaFact`): retrieval, fingers, or counting fingers.

Results:
* `columns_place_value`: with correct carrying, the answer is exactly
  units result + 10 × tens result + 100 × hundreds result. Carrying adds no
  error of its own.
* `columns_exact`: if every column is added correctly, so is the problem.
* `one_column_errs`: if only one column's addition can err, the problem is
  wrong exactly when that column is. An error of `δ` in the tens column
  makes the answer off by `10δ`, and in the hundreds column by `100δ`.
* `doaFact_wrong`, `column_error_is_doa_error`: with DOA as the
  single-digit process, a column errs as often as the single-digit DOA
  trial on its digits, and the problem then errs exactly as often.

Simplifications: carrying is error-free, and the columns are added
independently of one another.
-/

import MultiDigit.Postulates
import StrategyChoice

namespace MD

open Cog Dist

/-- **M4 Column backup.** Add each column with `fact`, units first, carrying
the tens of each column's result into the next. -/
def columns (fact : Nat → Nat → Dist Nat) (p : Problem) : Dist Nat :=
  Dist.bind (fact (p.digit .first .units) (p.digit .second .units)) fun r0 =>
  Dist.bind (fact (p.digit .first .tens) (p.digit .second .tens)) fun r1 =>
  Dist.bind (fact (p.digit .first .hundreds) (p.digit .second .hundreds)) fun r2 =>
    Dist.pure ((r2 + (r1 + r0 / 10) / 10) * 100 + (r1 + r0 / 10) % 10 * 10 + r0 % 10)

/-- **Place value.** With correct carrying, the answer is the column results
weighted by place: carrying adds no error of its own. -/
theorem columns_place_value (fact : Nat → Nat → Dist Nat) (p : Problem) :
    columns fact p =
      Dist.bind (fact (p.digit .first .units) (p.digit .second .units)) fun r0 =>
      Dist.bind (fact (p.digit .first .tens) (p.digit .second .tens)) fun r1 =>
      Dist.bind (fact (p.digit .first .hundreds) (p.digit .second .hundreds)) fun r2 =>
        Dist.pure (r0 + 10 * r1 + 100 * r2) := by
  unfold columns
  congr 1; funext r0; congr 1; funext r1; congr 1; funext r2
  congr 1
  omega

/-- A single-digit process is *exact* on two digits when it surely gives
their sum. -/
def Exact (fact : Nat → Nat → Dist Nat) (d e : Nat) : Prop := fact d e = Dist.pure (d + e)

theorem sum_place_value (p : Problem) (ha : p.a < 1000) (hb : p.b < 1000) :
    p.sum = (p.digit .first .units + p.digit .second .units) +
      10 * (p.digit .first .tens + p.digit .second .tens) +
      100 * (p.digit .first .hundreds + p.digit .second .hundreds) := by
  simp only [Problem.sum, Problem.digit, Problem.addend, digitOf]
  omega

/-- **Correct columns, correct answer.** -/
theorem columns_exact (fact : Nat → Nat → Dist Nat) (p : Problem) (ha : p.a < 1000)
    (hb : p.b < 1000)
    (hu : Exact fact (p.digit .first .units) (p.digit .second .units))
    (ht : Exact fact (p.digit .first .tens) (p.digit .second .tens))
    (hh : Exact fact (p.digit .first .hundreds) (p.digit .second .hundreds)) :
    columns fact p = Dist.pure p.sum := by
  rw [columns_place_value, hu, bind_pure_left, ht, bind_pure_left, hh, bind_pure_left,
    sum_place_value p ha hb]

/-- **One column errs: the problem errs exactly when it does.** If two of the
columns are added exactly, the column backup is wrong exactly as often as
the remaining column's single-digit addition is. (`j` is the column that can
err.) -/
theorem one_column_errs (fact : Nat → Nat → Dist Nat) (p : Problem) (ha : p.a < 1000)
    (hb : p.b < 1000) (j : Place)
    (hex : ∀ j', j' ≠ j → Exact fact (p.digit .first j') (p.digit .second j')) :
    prob (columns fact p) (fun ans => ans != p.sum) =
      prob (fact (p.digit .first j) (p.digit .second j))
        (fun r => r != p.digit .first j + p.digit .second j) := by
  rw [columns_place_value, sum_place_value p ha hb]
  cases j with
  | units =>
    rw [hex .tens (by decide)]
    simp only [bind_pure_left]
    rw [hex .hundreds (by decide)]
    simp only [bind_pure_left, prob_bind_pure]
    apply prob_congr; intro r
    rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq]
    constructor <;> intro h <;> omega
  | tens =>
    rw [hex .units (by decide), bind_pure_left]
    rw [show (fun r1 => Dist.bind (fact (p.digit .first .hundreds) (p.digit .second .hundreds))
        fun r2 => Dist.pure (p.digit .first .units + p.digit .second .units + 10 * r1 + 100 * r2)) =
        (fun r1 => Dist.pure (p.digit .first .units + p.digit .second .units + 10 * r1 +
          100 * (p.digit .first .hundreds + p.digit .second .hundreds))) from by
      funext r1; rw [hex .hundreds (by decide), bind_pure_left]]
    rw [prob_bind_pure]
    apply prob_congr; intro r
    rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq]
    constructor <;> intro h <;> omega
  | hundreds =>
    rw [hex .units (by decide), bind_pure_left, hex .tens (by decide), bind_pure_left,
      prob_bind_pure]
    apply prob_congr; intro r
    rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq]
    constructor <;> intro h <;> omega

/-- **The single-digit process as a DOA trial**: the answer of
`SC.trial` on the problem `d + e`, with that problem's associations. -/
def doaFact (as : List Nat) (s : SC.Problem → Nat → Rat) (bk : SC.Backup) (cc : Rat) (n : Nat)
    (d e : Nat) : Dist Nat :=
  Dist.bind (SC.trial as (s ⟨d, e⟩) bk cc n ⟨d, e⟩) fun o => Dist.pure o.2

/-- With DOA as the single-digit process, a column errs exactly as often as
the DOA trial on its digits does, whatever strategy that trial uses. -/
theorem doaFact_wrong (as : List Nat) (s : SC.Problem → Nat → Rat) (bk : SC.Backup) (cc : Rat)
    (n d e : Nat) :
    prob (doaFact as s bk cc n d e) (fun r => r != d + e) =
      prob (SC.trial as (s ⟨d, e⟩) bk cc n ⟨d, e⟩) (fun o => o.2 != d + e) :=
  prob_bind_pure _ _ _

/-- Proper single-digit processes make a proper column backup. -/
theorem mass_columns (fact : Nat → Nat → Dist Nat) (hf : ∀ d e, mass (fact d e) = 1)
    (p : Problem) : mass (columns fact p) = 1 :=
  mass_bind _ _ (hf _ _) fun _ => mass_bind _ _ (hf _ _) fun _ =>
    mass_bind _ _ (hf _ _) fun _ => mass_pure _

/-- The DOA single-digit process is proper when its associations, and those
elaborated on the fingers, have positive total strength. -/
theorem mass_doaFact (as : List Nat) (s : SC.Problem → Nat → Rat) (bk : SC.Backup) (cc : Rat)
    (n d e : Nat) (hT : total as (s ⟨d, e⟩) ≠ 0)
    (hE : total as (SC.elaborate (s ⟨d, e⟩) (d + e) bk.e) ≠ 0) :
    mass (doaFact as s bk cc n d e) = 1 :=
  mass_bind _ _ (SC.mass_trial as _ bk cc n ⟨d, e⟩ hT hE) fun _ => mass_pure _

theorem nonneg_columns (fact : Nat → Nat → Dist Nat) (hf : ∀ d e, Nonneg (fact d e))
    (p : Problem) : Nonneg (columns fact p) :=
  nonneg_bind _ _ (hf _ _) fun _ => nonneg_bind _ _ (hf _ _) fun _ =>
    nonneg_bind _ _ (hf _ _) fun _ => nonneg_pure _

theorem nonneg_doaFact (as : List Nat) (s : SC.Problem → Nat → Rat) (bk : SC.Backup) (cc : Rat)
    (n d e : Nat) (hs : ∀ a, 0 ≤ s ⟨d, e⟩ a) (he : 0 ≤ bk.e) (h1 : 0 ≤ bk.qs) (h2 : 0 ≤ bk.qd)
    (h3 : 0 ≤ 1 - bk.qs - bk.qd) : Nonneg (doaFact as s bk cc n d e) :=
  nonneg_bind _ _ (SC.nonneg_trial as _ bk cc n ⟨d, e⟩ hs he h1 h2 h3) fun _ => nonneg_pure _

/-- **A column error is a single-digit DOA error, moved to its place.** With
DOA adding the columns, if two columns are certain, the problem is wrong
exactly as often as the DOA trial on the third column's digits. -/
theorem column_error_is_doa_error (as : List Nat) (s : SC.Problem → Nat → Rat) (bk : SC.Backup)
    (cc : Rat) (n : Nat) (p : Problem) (ha : p.a < 1000) (hb : p.b < 1000) (j : Place)
    (hex : ∀ j', j' ≠ j → Exact (doaFact as s bk cc n) (p.digit .first j') (p.digit .second j')) :
    prob (columns (doaFact as s bk cc n) p) (fun ans => ans != p.sum) =
      prob (SC.trial as (s ⟨p.digit .first j, p.digit .second j⟩) bk cc n
        ⟨p.digit .first j, p.digit .second j⟩)
        (fun o => o.2 != p.digit .first j + p.digit .second j) :=
  (one_column_errs _ p ha hb j hex).trans (doaFact_wrong as s bk cc n _ _)

end MD
