/-
Representations: terms, the values of a knowledge net.

A term is an atom (a concept, an object, a button), a structured value
(`setPlan [moveForward9]`: "set the program-plan to MOVE FORWARD 9"), or a
*hole* of a given type, an unfilled place (`hole RWA`: "a Real-World-Action").
A term with holes is a pattern. Matching a pattern against a value binds
its holes (`unify`); filling a pattern replaces holes by their bindings
(`fill`); renaming replaces atoms throughout (`rename`).

Main result: renaming by the identity changes nothing (`rename_id`).
-/

namespace Cog

inductive Term (A : Type) where
  | atom : A → Term A
  | app : A → List (Term A) → Term A
  | hole : A → Term A

namespace Term

variable {A : Type} [DecidableEq A]

mutual
def decEq : (s t : Term A) → Decidable (s = t)
  | .atom a, .atom b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .hole a, .hole b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .app f ss, .app g ts =>
    if h : f = g then
      match decEqList ss ts with
      | isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h' => isFalse (by intro e; cases e; exact h' rfl)
    else isFalse (by intro e; cases e; exact h rfl)
  | .atom _, .app _ _ => isFalse (by intro e; cases e)
  | .atom _, .hole _ => isFalse (by intro e; cases e)
  | .app _ _, .atom _ => isFalse (by intro e; cases e)
  | .app _ _, .hole _ => isFalse (by intro e; cases e)
  | .hole _, .atom _ => isFalse (by intro e; cases e)
  | .hole _, .app _ _ => isFalse (by intro e; cases e)
def decEqList : (ss ts : List (Term A)) → Decidable (ss = ts)
  | [], [] => isTrue rfl
  | s :: ss, t :: ts =>
    match decEq s t, decEqList ss ts with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h' => isFalse (by intro e; cases e; exact h' rfl)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq (Term A) := decEq

/-- Bindings of hole types to terms. -/
abbrev Subst (A : Type) := List (A × Term A)

mutual
/-- Match a pattern against a value: the bindings of its holes, if it fits. -/
def unify : Term A → Term A → Option (Subst A)
  | .hole τ, v => some [(τ, v)]
  | .atom a, .atom b => if a = b then some [] else none
  | .app f ps, .app g vs => if f = g then unifyList ps vs else none
  | _, _ => none
def unifyList : List (Term A) → List (Term A) → Option (Subst A)
  | [], [] => some []
  | p :: ps, v :: vs =>
    match unify p v, unifyList ps vs with
    | some s, some s' => some (s ++ s')
    | _, _ => none
  | _, _ => none
end

mutual
/-- Fill a pattern's holes from bindings; unbound holes stay. -/
def fill (σ : Subst A) : Term A → Term A
  | .hole τ => (σ.lookup τ).getD (.hole τ)
  | .atom a => .atom a
  | .app f ps => .app f (fillList σ ps)
def fillList (σ : Subst A) : List (Term A) → List (Term A)
  | [] => []
  | p :: ps => fill σ p :: fillList σ ps
end

mutual
/-- Rename atoms throughout. -/
def rename (r : A → A) : Term A → Term A
  | .atom a => .atom (r a)
  | .hole τ => .hole τ
  | .app f ps => .app f (renameList r ps)
def renameList (r : A → A) : List (Term A) → List (Term A)
  | [] => []
  | p :: ps => rename r p :: renameList r ps
end

mutual
/-- The atoms occurring in a term. -/
def atoms : Term A → List A
  | .atom a => [a]
  | .hole _ => []
  | .app _ ps => atomsList ps
def atomsList : List (Term A) → List A
  | [] => []
  | p :: ps => atoms p ++ atomsList ps
end

/-- Remove the atoms satisfying `drop` from the arguments of every structured
value. -/
def dropAtoms (drop : A → Bool) : Term A → Term A
  | .app f ps => .app f (ps.filter fun p => match p with
      | .atom a => !drop a
      | _ => true)
  | t => t

/-- Whether a term has holes (is a pattern). -/
def hasHole : Term A → Bool
  | .hole _ => true
  | .atom _ => false
  | .app _ ps => ps.any fun p => match p with
      | .hole _ => true
      | _ => false

omit [DecidableEq A] in
mutual
theorem rename_id (t : Term A) : rename id t = t := by
  cases t with
  | atom a => rfl
  | hole τ => rfl
  | app f ps => simp only [rename]; rw [renameList_id ps]
theorem renameList_id (ps : List (Term A)) : renameList id ps = ps := by
  cases ps with
  | nil => rfl
  | cons p ps => simp only [renameList]; rw [rename_id p, renameList_id ps]
end

end Term

end Cog
