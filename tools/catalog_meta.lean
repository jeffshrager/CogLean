/-
Used by `gen_catalog.py` (appended after the package's imports); not part of
any library. For every theorem defined in the package's modules, prints one
line: name | module | quantified | negated | law | law module | axioms ok |
docstring's first sentence.

* quantified: the statement binds variables (a claim for every value of
  them); otherwise it is a closed statement, a single computed case.
Lemmas Lean generates itself (equation lemmas, `sizeOf_spec`, `injEq`, ...)
are skipped.

* law: the head of the conclusion (under `¬` and `∃`), when it is a
  definition from a `CogLib.Phenomena` module, a theory-neutral phenomenon.
-/

open Lean Meta

def catStd : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def catSkip (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
  (match n with
   | .str _ s => s.startsWith "eq_" || s == "eq_def" || s.startsWith "induct" ||
       s.startsWith "match_" || s.startsWith "proof_" || s == "mutual_induct" ||
       s == "sizeOf_spec" || s == "ofNat_ctorIdx" || s == "congr_simp" || s == "injEq" ||
       s == "inj" || s == "ext" || s == "ext_iff" || s.endsWith "_def" || s == "fun_cases" ||
       s.startsWith "_" || s == "ctorIdx_eq"
   | _ => false)

partial def catHead (e : Expr) : MetaM (Bool × Option Name) := do
  let e ← whnfR e
  if e.isAppOfArity ``Not 1 then
    let (_, h) ← catHead e.appArg!
    return (true, h)
  if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam n t b bi => return (← withLocalDecl n bi t fun x => catHead (b.instantiate1 x))
    | _ => return (false, none)
  return (false, e.getAppFn.constName?)

def catLine (prefixes : List Name) : MetaM Unit := do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let .thmInfo _ := ci | continue
    if catSkip n then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless prefixes.any (fun p => p.isPrefixOf mod) do continue
    let (q, neg, law) ← forallTelescope ci.type fun xs body => do
      let (neg, h) ← catHead body
      return (decide (xs.size > 0), neg, h)
    let lawMod : String := match law with
      | some l => match env.getModuleIdxFor? l with
        | some i => toString env.header.moduleNames[i.toNat]!
        | none => ""
      | none => ""
    let ax ← collectAxioms n
    let ok := ax.all (catStd.contains ·)
    let doc := ((← findDocString? env n).getD "").replace "\n" " " |>.replace "|" "/"
    let lawS := match law with | some l => toString l | none => ""
    IO.println s!"{n}|{mod}|{q}|{neg}|{lawS}|{lawMod}|{ok}|{doc}"
