# Brief for the independent layer audit

You are auditing CogLean, a library of cognitive theory in the Lean 4 proof assistant, for
how well its code is factored into layers. You have not worked on this code. Judge it fresh.
You can read files but not change them. Your report is published verbatim in the release
audit, followed by a separate response from the authors.

## What CogLean is

The repository is at the path you are given (call it `ROOT`).
- `ROOT/CogLib/` is the general library: representations, mechanisms, theory-neutral
  phenomena and laws, and general theorems.
- Every other top-level package (`EPAM/`, `StrategyChoice/`, `MultiDigit/`, `CogMatrix/`,
  `Experiments/`, `Concepts/`, `SemanticMemory/`, `ViewApplication/`, `DeviceLearning/`,
  `Sims/`, `ACTR/`) builds on CogLib. Each is a theory, an application, or a tool.
- `ROOT/README.md` and each package's `README.md` describe them.

## The standard

Read `ROOT/notes/LAYERING_POLICY.md` first. Audit against it. Where the policy is silent or
seems wrong, say so as a finding in the `policy` category, but don't invent rules.

## Your inputs

1. `ROOT/notes/audits/<tag>/MECHANICAL.md`: the mechanical audit for this release, from
   `tools/audit_layers.py`. It covers dependencies, metrics, task vocabulary in CogLib,
   concrete settings, duplication, relabellings, promotion candidates, fan-out, and proof
   trees: what each headline theorem's proof rests on, generic lemmas outside CogLib, and
   repeated proof shapes across packages.
2. `ROOT/notes/audits/FINDINGS.md`, if it exists: findings from earlier audits, with their
   statuses.
3. The code.

## What to do

1. **Triage the mechanical flags.** For each section of `MECHANICAL.md`, say which flags
   are real problems, which are acceptable under the policy (and why), and which are noise
   from the tool. Don't repeat the whole list; group them.
2. **Review CogLib module by module**, for what the script can't see:
   - task or theory content in general vocabulary, such as a "general" definition whose
     shape only makes sense for one task;
   - a mechanism that hard-codes one theory's commitments where a parameter would do;
   - near-duplicate definitions or theorems within CogLib;
   - constructs in the wrong module or layer;
   - names that hide generality, or claim generality that isn't there;
   - docstrings that describe one application rather than the construct.
3. **Review the packages above CogLib** for generic machinery that should move down.
   Use the proof-tree section: lemmas in headline proof trees that use only CogLib, repeated
   proof shapes, and headline theorems whose proofs rest mostly on their own package.
4. **Check earlier findings.** For each open finding in `FINDINGS.md`, say whether it is
   still present, resolved, or changed.
5. **Recommend.** Rank the three to five changes that would most improve the factoring.

Be concrete. Cite files and line numbers, or Lean names. Don't propose changes to the
science (what the theories claim), only to where things live and how they are named and
shared.

## Output format

Return Markdown with these sections, in order.

```
## Summary
(one paragraph)

## Triage of the mechanical flags
(by section of MECHANICAL.md)

## Findings
### <short title>
- Category: leakage | refactor | duplication | placement | naming | dependency | policy
- Severity: high | medium | low
- Location: <files and lines, or Lean names>
- Evidence: <what you saw>
- Proposed patch: <what moves where, what is renamed, which statements change, which
  dependents must be updated, and the expected effect; a sketch, not code>
- Prior: new | F### (if this revisits an earlier finding)
- Status: (for a prior finding) still open | resolved | changed

(one block per finding)

## Earlier findings
(one line per open finding in FINDINGS.md)

## Recommendations
(three to five, ranked)
```

Severity:
- **high**: task or theory content in CogLib, or a dependency violation;
- **medium**: duplication or misplacement that will grow if left;
- **low**: naming and tidiness.
