/-
GPS on multi-column addition, for every problem, and the same knowledge
deficit under two control regimes. Builds on `MultiDigit/Solver.lean` and
CogLib's means-ends analysis lemmas (`achieve_chain_step`,
`achieve_chain_fail_sub`, `achieve_chain_fail_pre`, `achieve_done`).

Single-digit facts are exact here (`exact`): the theorems are about the
control regime, not about errors in the facts.
-/

import MultiDigit.Solver

namespace MD.Solver

open Cog

/-! ### GPS for every problem (exact single-digit facts) -/

/-- The state after adding column `i` with exact facts. -/
def addSt (i : Nat) (s : St) : St :=
  { s with sum := some (s.p.digit .first (placeOf i) + s.p.digit .second (placeOf i) + s.carry) }

theorem apply_add_exact (i : Nat) (s : St) :
    (space exact).apply (.add i) s = Dist.pure (addSt i s) := by
  simp [space, exact, addSt, Dist.bind_pure_left]

/-- The digit sum of column `i`. -/
def colSum (p : Problem) (i : Nat) : Nat := p.digit .first (placeOf i) + p.digit .second (placeOf i)

/-- The column sums with carries, and the final carry. -/
def v0 (p : Problem) : Nat := colSum p 0 + 0
def v1 (p : Problem) : Nat := colSum p 1 + v0 p / 10
def v2 (p : Problem) : Nat := colSum p 2 + v1 p / 10

/-- The states GPS passes through with full knowledge, written out. -/
def fa0 (p : Problem) : St := ⟨p, 0, 0, some (v0 p), [], false⟩
def fw0 (p : Problem) : St := ⟨p, 1, v0 p / 10, none, [[v0 p % 10]], false⟩
def fa1 (p : Problem) : St := ⟨p, 1, v0 p / 10, some (v1 p), [[v0 p % 10]], false⟩
def fw1 (p : Problem) : St := ⟨p, 2, v1 p / 10, none, [[v0 p % 10], [v1 p % 10]], false⟩
def fa2 (p : Problem) : St := ⟨p, 2, v1 p / 10, some (v2 p), [[v0 p % 10], [v1 p % 10]], false⟩
def fw2 (p : Problem) : St := ⟨p, 3, v2 p / 10, none, [[v0 p % 10], [v1 p % 10], [v2 p % 10]], false⟩

theorem gps_a0 (p : Problem) (k : Nat) :
    achieve (space exact) gpsMEA (k + 1 + 1) [.summed 0] (init p) = Dist.pure (some (fa0 p)) := by
  rw [achieve_chain_step (space exact) gpsMEA (k + 1) [.summed 0] (init p) (init p) (fa0 p) (.summed 0) (.add 0) [] rfl rfl rfl
    (achieve_done _ _ k _ _ rfl) rfl (by rw [apply_add_exact]; rfl)]
  exact achieve_done _ _ k _ _ rfl

theorem gps_w0 (p : Problem) (k : Nat) :
    achieve (space exact) gpsMEA (k + 1 + 1 + 1) [.written 0] (init p) = Dist.pure (some (fw0 p)) := by
  rw [achieve_chain_step (space exact) gpsMEA (k + 1 + 1) [.written 0] (init p) (fa0 p) (fw0 p) (.written 0) (.writeCarry 0) [.summed 0] rfl rfl rfl
    (gps_a0 p k) rfl (by rw [apply_writeCarry exact 0 (v0 p) _ rfl]; rfl)]
  exact achieve_done _ _ (k + 1) _ _ rfl

theorem gps_a1 (p : Problem) (k : Nat) :
    achieve (space exact) gpsMEA (k + 1 + 1 + 1 + 1) [.summed 1] (init p) = Dist.pure (some (fa1 p)) := by
  rw [achieve_chain_step (space exact) gpsMEA (k + 1 + 1 + 1) [.summed 1] (init p) (fw0 p) (fa1 p) (.summed 1) (.add 1) [.written 0] rfl rfl rfl
    (gps_w0 p k) rfl (by rw [apply_add_exact]; rfl)]
  exact achieve_done _ _ (k + 1 + 1) _ _ rfl

theorem gps_w1 (p : Problem) (k : Nat) :
    achieve (space exact) gpsMEA (k + 1 + 1 + 1 + 1 + 1) [.written 1] (init p) = Dist.pure (some (fw1 p)) := by
  rw [achieve_chain_step (space exact) gpsMEA (k + 1 + 1 + 1 + 1) [.written 1] (init p) (fa1 p) (fw1 p) (.written 1) (.writeCarry 1) [.summed 1]
    rfl rfl rfl (gps_a1 p k) rfl (by rw [apply_writeCarry exact 1 (v1 p) _ rfl]; rfl)]
  exact achieve_done _ _ (k + 1 + 1 + 1) _ _ rfl

theorem gps_a2 (p : Problem) (k : Nat) :
    achieve (space exact) gpsMEA (k + 1 + 1 + 1 + 1 + 1 + 1) [.summed 2] (init p) =
      Dist.pure (some (fa2 p)) := by
  rw [achieve_chain_step (space exact) gpsMEA (k + 1 + 1 + 1 + 1 + 1) [.summed 2] (init p) (fw1 p) (fa2 p) (.summed 2) (.add 2) [.written 1] rfl rfl rfl
    (gps_w1 p k) rfl (by rw [apply_add_exact]; rfl)]
  exact achieve_done _ _ (k + 1 + 1 + 1 + 1) _ _ rfl

theorem gps_w2 (p : Problem) (k : Nat) :
    achieve (space exact) gpsMEA (k + 1 + 1 + 1 + 1 + 1 + 1 + 1) [.written 2] (init p) =
      Dist.pure (some (fw2 p)) := by
  rw [achieve_chain_step (space exact) gpsMEA (k + 1 + 1 + 1 + 1 + 1 + 1) [.written 2] (init p) (fa2 p) (fw2 p) (.written 2)
    (.writeCarry 2) [.summed 2] rfl rfl rfl (gps_a2 p k) rfl (by rw [apply_writeCarry exact 2 (v2 p) _ rfl]; rfl)]
  exact achieve_done _ _ (k + 1 + 1 + 1 + 1 + 1) _ _ rfl

theorem gps_finished (p : Problem) (k : Nat) :
    achieve (space exact) gpsMEA (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) [.finished] (init p) =
      Dist.pure (some (finishSt (fw2 p))) := by
  rw [achieve_chain_step (space exact) gpsMEA (k + 1 + 1 + 1 + 1 + 1 + 1 + 1) [.finished] (init p) (fw2 p) (finishSt (fw2 p))
    .finished .finish [.written 2] rfl rfl rfl (gps_w2 p k) rfl (apply_finish exact _)]
  exact achieve_done _ _ (k + 1 + 1 + 1 + 1 + 1 + 1) _ _ rfl

/-- **GPS adds the columns units first, for every problem**, and finishes. Its
goal is only to be finished; the order comes from subgoaling on
preconditions: finishing needs the hundreds written, writing a column needs
its sum, adding a column needs the column to its right written. The state
it reaches writes the cells units, then tens, then hundreds. -/
theorem gps_every_problem (p : Problem) :
    gpsAnswers exact p = Dist.pure (some (answer (finishSt (fw2 p)))) := by
  unfold gpsAnswers
  rw [show (12 : Nat) = 4 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl, gps_finished p 4, Dist.bind_pure_left]
  rfl

/-- **GPS answers exactly**: for every problem with 3-digit addends, the sum. -/
theorem gps_exact (p : Problem) (ha : p.a < 1000) (hb : p.b < 1000) :
    gpsAnswers exact p = Dist.pure (some p.sum) := by
  rw [gps_every_problem, sum_place_value p ha hb]
  congr 2
  simp only [answer, finishSt, fw2, v2, v1, v0, colSum, placeOf]
  by_cases h : (p.digit .first .hundreds + p.digit .second .hundreds +
      (p.digit .first .tens + p.digit .second .tens + (p.digit .first .units + p.digit .second .units + 0) / 10) / 10) / 10 = 0 <;>
    simp only [h, ite_true, ite_false, List.nil_append, List.cons_append, List.append_nil, readOut,
      List.foldl_cons, List.foldl_nil, List.length_singleton, Nat.max_self, Nat.pow_one, Nat.one_mul,
      Nat.zero_mul, Nat.zero_add] <;> omega

/-! ### The same knowledge deficit under two control regimes -/

/-- The states GPS passes through without the carry operator, written out:
each column's whole sum in its cell, nothing carried. -/
def na0 (p : Problem) : St := ⟨p, 0, 0, some (colSum p 0 + 0), [], false⟩
def nw0 (p : Problem) : St := ⟨p, 1, 0, none, [[colSum p 0 + 0]], false⟩
def na1 (p : Problem) : St := ⟨p, 1, 0, some (colSum p 1 + 0), [[colSum p 0 + 0]], false⟩
def nw1 (p : Problem) : St := ⟨p, 2, 0, none, [[colSum p 0 + 0], [colSum p 1 + 0]], false⟩
def na2 (p : Problem) : St := ⟨p, 2, 0, some (colSum p 2 + 0), [[colSum p 0 + 0], [colSum p 1 + 0]], false⟩
def nw2 (p : Problem) : St :=
  ⟨p, 3, 0, none, [[colSum p 0 + 0], [colSum p 1 + 0], [colSum p 2 + 0]], false⟩

theorem write_pre (i : Nat) (s : St) (v : Nat) (hc : s.col = i) (h : s.sum = some v) :
    (space exact).pre (.write i) s = decide (v < 10) := by
  simp [space, hc, h]

theorem ngps_a0 (p : Problem) (k : Nat) :
    achieve (space exact) gpsNoCarry (k + 1 + 1) [.summed 0] (init p) = Dist.pure (some (na0 p)) := by
  rw [achieve_chain_step (space exact) gpsNoCarry (k + 1) [.summed 0] (init p) (init p) (na0 p) (.summed 0) (.add 0) [] rfl rfl rfl
    (achieve_done _ _ k _ _ rfl) rfl (by rw [apply_add_exact]; rfl)]
  exact achieve_done _ _ k _ _ rfl

/-- Without the carry operator, GPS gets past column 0 only if its digits sum
to less than 10. -/
theorem ngps_w0 (p : Problem) (k : Nat) :
    achieve (space exact) gpsNoCarry (k + 1 + 1 + 1) [.written 0] (init p) =
      if colSum p 0 < 10 then Dist.pure (some (nw0 p)) else Dist.pure none := by
  have hpre := write_pre 0 (na0 p) (colSum p 0 + 0) rfl rfl
  by_cases h : colSum p 0 < 10
  · rw [achieve_chain_step (space exact) gpsNoCarry (k + 1 + 1) [.written 0] (init p) (na0 p) (nw0 p) (.written 0) (.write 0) [.summed 0] rfl rfl rfl
      (ngps_a0 p k) (by rw [hpre]; simpa using h) (by rw [apply_write exact 0 _ _ rfl]; rfl)]
    rw [ite_eq_left h]; exact achieve_done _ _ (k + 1) _ _ rfl
  · rw [achieve_chain_fail_pre (space exact) gpsNoCarry (k + 1 + 1) [.written 0] (init p) (na0 p) (.written 0) (.write 0) [.summed 0] rfl rfl rfl
      (ngps_a0 p k) (by rw [hpre]; simpa using h), ite_eq_right h]

theorem ngps_a1 (p : Problem) (k : Nat) :
    achieve (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1) [.summed 1] (init p) =
      if colSum p 0 < 10 then Dist.pure (some (na1 p)) else Dist.pure none := by
  by_cases h : colSum p 0 < 10
  · have hw := ngps_w0 p k; rw [ite_eq_left h] at hw
    rw [achieve_chain_step (space exact) gpsNoCarry (k + 1 + 1 + 1) [.summed 1] (init p) (nw0 p) (na1 p) (.summed 1) (.add 1) [.written 0] rfl rfl rfl
      hw rfl (by rw [apply_add_exact]; rfl), ite_eq_left h]
    exact achieve_done _ _ (k + 1 + 1) _ _ rfl
  · have hw := ngps_w0 p k; rw [ite_eq_right h] at hw
    rw [achieve_chain_fail_sub (space exact) gpsNoCarry (k + 1 + 1 + 1) [.summed 1] (init p) (.summed 1) (.add 1) [.written 0] rfl rfl rfl hw, ite_eq_right h]

theorem ngps_w1 (p : Problem) (k : Nat) :
    achieve (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1 + 1) [.written 1] (init p) =
      if colSum p 0 < 10 ∧ colSum p 1 < 10 then Dist.pure (some (nw1 p)) else Dist.pure none := by
  by_cases h0 : colSum p 0 < 10
  · have ha := ngps_a1 p k; rw [ite_eq_left h0] at ha
    have hpre := write_pre 1 (na1 p) (colSum p 1 + 0) rfl rfl
    by_cases h1 : colSum p 1 < 10
    · rw [achieve_chain_step (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1) [.written 1] (init p) (na1 p) (nw1 p) (.written 1) (.write 1) [.summed 1] rfl rfl rfl
        ha (by rw [hpre]; simpa using h1) (by rw [apply_write exact 1 _ _ rfl]; rfl),
        ite_eq_left ⟨h0, h1⟩]
      exact achieve_done _ _ (k + 1 + 1 + 1) _ _ rfl
    · rw [achieve_chain_fail_pre (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1) [.written 1] (init p) (na1 p) (.written 1) (.write 1) [.summed 1] rfl rfl rfl
        ha (by rw [hpre]; simpa using h1), ite_eq_right (fun h => h1 h.2)]
  · have ha := ngps_a1 p k; rw [ite_eq_right h0] at ha
    rw [achieve_chain_fail_sub (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1) [.written 1] (init p) (.written 1) (.write 1) [.summed 1] rfl rfl rfl ha,
      ite_eq_right (fun h => h0 h.1)]

theorem ngps_a2 (p : Problem) (k : Nat) :
    achieve (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1 + 1 + 1) [.summed 2] (init p) =
      if colSum p 0 < 10 ∧ colSum p 1 < 10 then Dist.pure (some (na2 p)) else Dist.pure none := by
  by_cases h : colSum p 0 < 10 ∧ colSum p 1 < 10
  · have hw := ngps_w1 p k; rw [ite_eq_left h] at hw
    rw [achieve_chain_step (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1 + 1) [.summed 2] (init p) (nw1 p) (na2 p) (.summed 2) (.add 2) [.written 1] rfl rfl rfl
      hw rfl (by rw [apply_add_exact]; rfl), ite_eq_left h]
    exact achieve_done _ _ (k + 1 + 1 + 1 + 1) _ _ rfl
  · have hw := ngps_w1 p k; rw [ite_eq_right h] at hw
    rw [achieve_chain_fail_sub (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1 + 1) [.summed 2] (init p) (.summed 2) (.add 2) [.written 1] rfl rfl rfl hw, ite_eq_right h]

/-- Every column sums to less than 10: no carry is ever needed. -/
def NoCarryNeeded (p : Problem) : Prop := colSum p 0 < 10 ∧ colSum p 1 < 10 ∧ colSum p 2 < 10

instance (p : Problem) : Decidable (NoCarryNeeded p) := by unfold NoCarryNeeded; infer_instance

theorem ngps_w2 (p : Problem) (k : Nat) :
    achieve (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1 + 1 + 1 + 1) [.written 2] (init p) =
      if NoCarryNeeded p then Dist.pure (some (nw2 p)) else Dist.pure none := by
  by_cases h01 : colSum p 0 < 10 ∧ colSum p 1 < 10
  · have ha := ngps_a2 p k; rw [ite_eq_left h01] at ha
    have hs : (na2 p).sum = some (colSum p 2 + 0) := rfl
    have hpre := write_pre 2 (na2 p) (colSum p 2 + 0) rfl hs
    by_cases h2 : colSum p 2 < 10
    · rw [achieve_chain_step (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1 + 1 + 1) [.written 2] (init p) (na2 p) (nw2 p) (.written 2) (.write 2) [.summed 2]
        rfl rfl rfl ha (by rw [hpre]; simpa using h2) (by rw [apply_write exact 2 _ _ hs]; rfl), ite_eq_left ⟨h01.1, h01.2, h2⟩]
      exact achieve_done _ _ (k + 1 + 1 + 1 + 1 + 1) _ _ rfl
    · rw [achieve_chain_fail_pre (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1 + 1 + 1) [.written 2] (init p) (na2 p) (.written 2) (.write 2) [.summed 2] rfl rfl rfl
        ha (by rw [hpre]; simpa using h2), ite_eq_right (fun h => h2 h.2.2)]
  · have ha := ngps_a2 p k; rw [ite_eq_right h01] at ha
    rw [achieve_chain_fail_sub (space exact) gpsNoCarry (k + 1 + 1 + 1 + 1 + 1 + 1) [.written 2] (init p) (.written 2) (.write 2) [.summed 2] rfl rfl rfl ha,
      ite_eq_right (fun h => h01 ⟨h.1, h.2.1⟩)]

/-- **GPS without the carry operator gives up on carry problems, and is exact
on the rest**, for every problem. -/
theorem gps_noCarry (p : Problem) :
    gpsAnswersWith gpsNoCarry exact p =
      if NoCarryNeeded p then Dist.pure (some (answer (finishSt (nw2 p)))) else Dist.pure none := by
  unfold gpsAnswersWith
  rw [show (12 : Nat) = 3 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  by_cases h : NoCarryNeeded p
  · have hw := ngps_w2 p (3 + 1); rw [ite_eq_left h] at hw
    rw [achieve_chain_step (space exact) gpsNoCarry (3 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) [.finished] (init p) (nw2 p) (finishSt (nw2 p))
      .finished .finish [.written 2] rfl rfl rfl hw rfl (apply_finish exact _), achieve_done _ _ _ _ _ rfl,
      Dist.bind_pure_left, ite_eq_left h]
    rfl
  · have hw := ngps_w2 p (3 + 1); rw [ite_eq_right h] at hw
    rw [achieve_chain_fail_sub (space exact) gpsNoCarry (3 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) [.finished] (init p) .finished .finish [.written 2] rfl rfl rfl hw,
      Dist.bind_pure_left, ite_eq_right h]
    rfl

/-- **The same knowledge deficit, two control regimes.** Without the carry
rule, on every problem that needs a carry: the decision cycle with repair
(and strict critics) answers confidently and wrongly (`noCarry_bug`: the
no-carry answer), while GPS gives up, with no answer at all. On problems
needing no carry, both are exact. -/
theorem regimes_diverge (p : Problem) (h : ¬ NoCarryNeeded p) :
    gpsAnswersWith gpsNoCarry exact p = Dist.pure none ∧
      answers exact noCarry strict p = Dist.pure (noCarrySum p) := by
  rw [gps_noCarry, ite_eq_right h]
  exact ⟨rfl, noCarry_bug p⟩

end MD.Solver
