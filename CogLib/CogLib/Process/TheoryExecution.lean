/-
Processes: reading predictions off a theory held as a knowledge net.

A learner's theory of a device says what each key does through the value
of a slot of the key's frame (the *function* slot, as in Shrager 1987: the
BigTrak's Forward-9 has function "move forward 9"). To predict what a
sequence of key presses does, read each key's function term and apply its
denotation to the device state, in order. The denotations are task
knowledge, supplied as a parameter; nothing here mentions a device.

A key whose function is unknown, or whose function has no denotation,
makes the prediction `none`: the theory does not say.

Main results: a prediction depends on the theory only through the
function slots of the keys pressed (`predict_congr`); predictions of a
sequence compose (`predict_append`).
-/

import CogLib.Process.ViewApplication

namespace Cog

variable {A L S : Type} [DecidableEq A] [DecidableEq L]

/-- **Predict**: fold the denotations of the pressed keys' function terms
over the device state. `none` if the theory says nothing about some key. -/
def predict (fnL : L) (den : Term A → S → Option S) (T : KNet A L) : List A → S → Option S
  | [], s => some s
  | k :: ks, s => match T.slot k fnL with
    | none => none
    | some f => match den f s with
      | none => none
      | some s' => predict fnL den T ks s'

/-- **A prediction depends only on the pressed keys' function slots.** Two
theories that agree on those slots predict alike, whatever else they say. -/
theorem predict_congr (fnL : L) (den : Term A → S → Option S) (T T' : KNet A L) (keys : List A)
    (h : ∀ k ∈ keys, T.slot k fnL = T'.slot k fnL) (s : S) :
    predict fnL den T keys s = predict fnL den T' keys s := by
  induction keys generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [predict, h k (List.mem_cons_self ..)]
    split
    · rfl
    · split
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
