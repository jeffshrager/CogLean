/-
Processes: reading predictions off a theory held as a knowledge net.

One way a theory can predict (`Process/TheoryRevision` leaves this open):
each action is a frame whose *function* slot says what it does (as in
Shrager 1987, where the BigTrak's Forward-9 has function "move forward 9"),
and the denotation of that term, supplied as task knowledge, acts on a
state. A sequence of actions is predicted by applying the denotations in
order. This is a model of sequential, deterministic action; others are
possible.

An action whose function is unknown, or has no denotation, makes the
prediction `none`: the theory does not say.

Main results: a prediction depends on the theory only through the
function slots of the actions taken (`predict_congr`); predictions of a
sequence compose (`predict_append`).
-/

import CogLib.Process.ViewApplication

namespace Cog

variable {A L S : Type} [DecidableEq A] [DecidableEq L]

/-- **Predict**: fold the denotations of the actions' function terms over
the state. `none` if the theory says nothing about some action. -/
def predict (fnL : L) (den : Term A → S → Option S) (T : KNet A L) : List A → S → Option S
  | [], s => some s
  | k :: ks, s => match T.slot k fnL with
    | none => none
    | some f => match den f s with
      | none => none
      | some s' => predict fnL den T ks s'

/-- **A prediction depends only on the actions' function slots.** Two
theories that agree on those slots predict alike, whatever else they say. -/
theorem predict_congr (fnL : L) (den : Term A → S → Option S) (T T' : KNet A L) (acts : List A)
    (h : ∀ k ∈ acts, T.slot k fnL = T'.slot k fnL) (s : S) :
    predict fnL den T acts s = predict fnL den T' acts s := by
  induction acts generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [predict, h k (List.mem_cons_self ..)]
    split
    · rfl
    · split
      · rfl
      · exact ih (fun k' hk => h k' (List.mem_cons_of_mem _ hk)) _

/-- **Predict, with denotations that may read the theory.** The denotation
of an action's function term may also depend on the theory and on the
acting frame: for instance, on a slot of the action's type (what a number
it enters *means*). -/
def predictT (fnL : L) (den : KNet A L → A → Term A → S → Option S) (T : KNet A L) :
    List A → S → Option S
  | [], s => some s
  | k :: ks, s => match T.slot k fnL with
    | none => none
    | some f => match den T k f s with
      | none => none
      | some s' => predictT fnL den T ks s'

/-- `predict` is `predictT` with denotations that ignore the theory. -/
theorem predict_eq_predictT (fnL : L) (den : Term A → S → Option S) (T : KNet A L) (acts : List A)
    (s : S) : predict fnL den T acts s = predictT fnL (fun _ _ f => den f) T acts s := by
  induction acts generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [predict, predictT]
    split
    · rfl
    · split
      · rfl
      · exact ih _

/-- Two theories predict alike if they agree on the actions' function slots
and on what the denotations read of them. -/
theorem predictT_congr (fnL : L) (den : KNet A L → A → Term A → S → Option S) (T T' : KNet A L)
    (acts : List A)
    (h : ∀ k ∈ acts, T.slot k fnL = T'.slot k fnL ∧ ∀ f s, den T k f s = den T' k f s) (s : S) :
    predictT fnL den T acts s = predictT fnL den T' acts s := by
  induction acts generalizing s with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨h1, h2⟩ := h k (List.mem_cons_self ..)
    simp only [predictT, h1]
    split
    · rfl
    · rw [h2]
      split
      · rfl
      · exact ih (fun k' hk => h k' (List.mem_cons_of_mem _ hk)) _

/-- Predicting a sequence in two parts. -/
theorem predict_append (fnL : L) (den : Term A → S → Option S) (T : KNet A L) (ks ks' : List A)
    (s : S) :
    predict fnL den T (ks ++ ks') s = (predict fnL den T ks s).bind (predict fnL den T ks') := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.cons_append, predict]
    split
    · rfl
    · split
      · rfl
      · exact ih _

end Cog
