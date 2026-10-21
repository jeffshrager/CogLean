/-
Phenomena: responding to a cue, and how learning changes it.

A *responder* is what a theory of retrieval offers phenomena about: in each
state, a cue can evoke responses. It may be nondeterministic (more than one
response possible) and it may fail (`none`). A *probabilistic* responder says
how likely each response is; forgetting the numbers leaves a responder.

Phenomena of responding under learning, stated theory-neutrally:
* `RetroactiveInterference`: learning new material makes an old cue evoke
  the new material.
* `Oscillation`: after learning other material, a cue that evoked the right
  response can evoke a wrong one, and can still evoke the right one.

Like the other `Phenomena` modules, this names no mechanism. It uses only the
representation of finite distributions (`Rep/Distribution`).
-/

import CogLib.Rep.Distribution

namespace Cog

/-- A responder: in each state, which responses a cue can evoke (`none`: no
response). -/
structure Responder (State Cue Resp : Type) where
  CanRespond : State → Cue → Option Resp → Prop

/-- A probabilistic responder: in each state, a cue evokes a distribution of
responses. -/
structure ProbResponder (State Cue Resp : Type) where
  responses : State → Cue → Dist (Option Resp)

/-- The responses a probabilistic responder can give are those with positive
probability. -/
def ProbResponder.toResponder {State Cue Resp : Type} (R : ProbResponder State Cue Resp) :
    Responder State Cue Resp :=
  ⟨fun s c r => (R.responses s c).Possible r⟩

namespace Phenomena

variable {State Cue Resp Stim : Type}

/-- **Retroactive interference.** For some state, cue and responses `y ≠ w`:
the cue evokes `y`, and after `w` is learned the same cue can evoke `w`. -/
def RetroactiveInterference (R : Responder State Cue Resp) (study : State → Stim → State)
    (asResp : Stim → Resp) : Prop :=
  ∃ s c y w, y ≠ asResp w ∧ R.CanRespond s c (some y) ∧
    R.CanRespond (study s w) c (some (asResp w))

/-- **Oscillation.** For some state and cue that evoke the response `y`:
after other material `w` is learned, the cue can evoke a wrong response, and
can still evoke `y`. -/
def Oscillation (R : Responder State Cue Resp) (study : State → Stim → State) : Prop :=
  ∃ s c y w r, R.CanRespond s c (some y) ∧
    r ≠ some y ∧ R.CanRespond (study s w) c r ∧ R.CanRespond (study s w) c (some y)

end Phenomena
end Cog
