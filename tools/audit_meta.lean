/-
Used by `audit_layers.py` (appended after a package's imports); not part of any
library. For every declaration in the package's own modules, prints one line,
fields separated by U+001F:

  name, kind, module, quantified, closed def with a literal, statement hash,
  head of the proof or value, repo constants used (comma-separated), repo
  constants in the statement alone (comma-separated), headline (docstring
  begins in bold).
Auxiliary declarations (`foo._proof_1`, `foo.match_2`, …) print instead
`AUX`, the declaration they belong to, and the repo constants they use, so
that every proof tree is complete.

* kind: thm, def, opaque, axiom, inductive.
* quantified: for a theorem, whether the statement binds variables (otherwise
  it is a single computed case, an instance). For a def, whether its type
  binds variables.
* closed def with a literal: a def whose type binds nothing and whose value
  contains a numeric literal: a concrete setting.
* statement hash: the type's structural hash, which ignores binder names, so
  two theorems with the same statement have the same hash.
* head: the constant at the head of the value after its lambdas (for a proof
  that is one application of another theorem, that theorem).
* repo constants: constants in the type and value whose modules are in the
  repository's packages.
Lemmas Lean generates itself are skipped, as in `catalog_meta.lean`.
-/

open Lean Meta

def audRoots : List Name :=
  [`CogLib, `Epam, `StrategyChoice, `MultiDigit, `CogMatrix, `Experiments, `Concepts,
   `SemanticMemory, `ViewApplication, `DeviceLearning, `Sims, `ACTR]

def audSkip (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
  (match n with
   | .str _ s => s.startsWith "eq_" || s == "eq_def" || s.startsWith "induct" ||
       s.startsWith "match_" || s.startsWith "proof_" || s == "mutual_induct" ||
       s == "sizeOf_spec" || s == "ofNat_ctorIdx" || s == "congr_simp" || s == "injEq" ||
       s == "inj" || s == "ext" || s == "ext_iff" || s.endsWith "_def" || s == "fun_cases" ||
       s.startsWith "_" || s == "ctorIdx_eq" || s == "rec" || s == "recOn" || s == "casesOn" ||
       s == "noConfusion" || s == "noConfusionType" || s == "below" || s == "brecOn" ||
       s == "binductionOn" || s == "ibelow" || s == "mk" || s == "sizeOf_inst" ||
       s == "ctorIdx" || s.startsWith "instRepr" || s.startsWith "instDecidableEq" ||
       s.startsWith "instBEq" || s.startsWith "instInhabited" || s.startsWith "repr"
   | _ => false)

def audAuxComp (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
    s.startsWith "inst" || s == "decEq" || s == "eq_def" || s.startsWith "fun_cases"

/-- Strip auxiliary components (`._proof_1`, `.eq_1`, `.match_2`, `._f`, …) to reach the
user-written declaration they belong to. -/
partial def audBase : Name → Name
  | n@(.str p s) => if audAuxComp s then audBase p else n
  | n => n

def audAux (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => audAuxComp s
    | _ => false

def audModOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

def audInRepo (env : Environment) (n : Name) : Bool :=
  match audModOf env n with
  | some m => audRoots.any (·.isPrefixOf m)
  | none => false

partial def audHasLit (e : Expr) : Bool :=
  match e with
  | .lit _ => true
  | .app f a => audHasLit f || audHasLit a
  | .lam _ t b _ => audHasLit t || audHasLit b
  | .forallE _ t b _ => audHasLit t || audHasLit b
  | .letE _ t v b _ => audHasLit t || audHasLit v || audHasLit b
  | .mdata _ b => audHasLit b
  | .proj _ _ b => audHasLit b
  | _ => false

partial def audHead (e : Expr) : Option Name :=
  match e with
  | .lam _ _ b _ => audHead b
  | .mdata _ b => audHead b
  | _ => e.getAppFn.constName?

def audBinds (t : Expr) : Bool :=
  match t.consumeMData with
  | .forallE .. => true
  | _ => false

def audLine (prefixes : List Name) : MetaM Unit := do
  let env ← getEnv
  let sep := "\x1f"
  for (n, ci) in env.constants.toList do
    let some mod := audModOf env n | continue
    unless prefixes.any (·.isPrefixOf mod) do continue
    -- auxiliary proofs (`foo._proof_1`, `foo.match_2`, …): report their dependencies
    -- under the declaration they belong to, so its proof tree is complete
    if audAux n && !(audBase n).isAnonymous then
      let b := audBase n
      let used := (ci.getUsedConstantsAsSet.toList.map audBase).eraseDups.filter
        (fun c => c != b && audInRepo env c && !env.isProjectionFn c)
      IO.println s!"AUX{sep}{b}{sep}{",".intercalate (used.map toString)}"
      continue
    if audSkip n || env.isProjectionFn n then continue
    let kind : String := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | _ => ""
    if kind == "" then continue
    let q := audBinds ci.type
    let closedLit := kind == "def" && !q && (match ci.value? with
      | some v => audHasLit v | none => false)
    let head := match ci.value? with
      | some v => match audHead v with | some h => toString h | none => ""
      | none => ""
    let used := (ci.getUsedConstantsAsSet.toList.map audBase).eraseDups.filter
      (fun c => c != n && audInRepo env c && !env.isProjectionFn c)
    let usedS := ",".intercalate (used.map toString)
    let tyUsed := (ci.type.getUsedConstants.toList.map audBase).eraseDups.filter
      (fun c => c != n && audInRepo env c)
    let tyS := ",".intercalate (tyUsed.map toString)
    let doc := (← findDocString? env n).getD ""
    let headline := (doc.dropWhile Char.isWhitespace).startsWith "**"
    IO.println s!"{n}{sep}{kind}{sep}{mod}{sep}{q}{sep}{closedLit}{sep}{ci.type.hash}{sep}{head}{sep}{usedS}{sep}{tyS}{sep}{headline}"
