/-
Phenomena: the abstract learner they are stated about.

Phenomena are stated without reference to any mechanism, so that different
theories can be proved to have them or to lack them. What they need is only
an interface: a learner has states, it can study a stimulus (moving to a new
state), and in any state it recognizes each stimulus as something, or as
nothing.
-/

namespace Cog

/-- An incremental learner: studying a stimulus changes its state, and in
each state it recognizes a stimulus as some stimulus, or as nothing. -/
structure IncrementalLearner (State Stim : Type) where
  study : State → Stim → State
  recognizedAs : State → Stim → Option Stim

namespace IncrementalLearner

variable {State Stim : Type} (L : IncrementalLearner State Stim)

/-- A stimulus is recognized when it is recognized as itself. -/
def Recognizes (s : State) (x : Stim) : Prop := L.recognizedAs s x = some x

/-- Study a list of stimuli, in order. -/
def studyAll (s : State) (xs : List Stim) : State := xs.foldl L.study s

end IncrementalLearner
end Cog
