# Layer audit: 20261105-baseline

The first audit of CogLean's layering, run on the tree as of commit 2660f32 (after the ACT-R
paper and the audit tooling). It is a baseline, not a release: no git tag was created.

Policy: `notes/LAYERING_POLICY.md`. Files in this directory:
- `MECHANICAL.md`: the script's report;
- `metrics.json`, `rows.json`: the data;
- `REVIEW.md`: the independent review, verbatim;
- this file: the summary, the author response, and the decisions pending.

The ledger is `notes/audits/FINDINGS.md`.

## Summary

The dependencies are clean. There are no violations, and Mathlib appears only in ACTR. One
declared dependency is unused: ViewApplication requires Concepts but imports nothing from
it.

CogLib has no task words in identifiers by the vocabulary list. The independent review found
the leak the list misses: `whole` (as in "whole-problem") throughout the general
recognize-retrieve composition and the confusion-error phenomenon.

The review raised 12 findings (F001–F012):

| Severity | Findings |
|---|---|
| high (2) | F001: "whole-problem" vocabulary in CogLib. F004: `Phenomena/Combination` states its phenomena through one mechanism. |
| medium (7) | F002: MultiDigit's parallel trial and relabellings. F003: a missing merge-of-bind lemma. F005: library facts outside CogLib or scattered in it. F006: ViewApplication copies Concepts' number domain. F007: knowledge-net representation inside a Process module, and a categorizer with two models hard-coded. F008: two cue representations with no bridge. F011: memory families split between CogLib and CogMatrix. |
| low (3) | F009: serial anticipation inside `Control/Serial`. F010: hand-built one-hot strength tables. F012: policy and tool gaps. |

## Mechanical counts

| Check | Count |
|---|---|
| dependency violations | 0 |
| unused requires | 1 |
| identifier hits | 0 |
| docstring hits | 52 |
| CogLib instance theorems | 6 |
| CogLib closed defs with literals | 0 |
| same name across packages | 40 |
| same statement across packages | 8 |
| relabellings | 7 |
| promotion candidates | 52 |
| single-user CogLib defs | 10 |
| unused CogLib defs | 18 |
| headline proof trees | 211 |
| generic lemmas in headline trees | 8 |
| repeated proof shapes | 1 |
| near proof shapes | 1 |
| CogLib theorems with one user above | 43 |

No trend yet: this is the first audit.

The review judged most promotion, same-name and fan-out flags to be noise. The causes are
theory postulates that, by policy, mention only CogLib; homonyms in different namespaces; and
compiler-generated names. F012 lists the tool fixes.

## Independent review

See `REVIEW.md`. It covers the triage of every mechanical section, the 12 findings with
proposed patches, and five ranked recommendations.

## Author response

These are my responses as the main author of the code. I checked the review's central claims
against the source before answering:
- `Cog.Route` is `whole | backup`;
- the conjunction-effect phenomena are inequalities between `sim K S …`;
- `dsum3` and `ndigits` are byte-identical to `digitSum3` and `size`;
- `uniform` and `uniformOf` are identical;
- `Process/Categorize` and `Process/SpreadingActivation` import `Process/ViewApplication`.

- **F001 (agree, high).** "Whole" is MultiDigit's word (whole problem against columns) and
  survived when the composition was extracted into CogLib. The rename (`retrieved`, or
  `direct`) is mechanical and changes no statement. Do it first, since F002 depends on it.
  The papers use "whole route" as MultiDigit vocabulary, which stays.
- **F002 (agree).** The relabel map exists only because MultiDigit kept its own `Route`.
  Fold MultiDigit onto `Cog.recognizeRetrieve` after F001. Keep the `MD.*` theorems stated for
  the net (`N.select`); delete the `MD.AnyMemory` copies.
- **F003 (agree).** This is the repeated proof shape the proof-tree check found.
  `Dist.same_merge_bind` and `RR.same_backup` are small additions with eight users.
- **F004 (agree, high).** It breaks the one rule that defines `Phenomena/`. The abstract
  restatement is better science as well as better layering: it lets any theory of concepts be
  tested against the conjunction effect.
- **F005 (agree).** Some of the scattered helpers (`cast_nonneg`, `mul_le_mul_pos`,
  `natCast_pow_pos`, `sum_replicate_rat`) are from this week's learning-curve and priming
  work. A `CogLib/Basic.lean` is the right home.
- **F006 (agree).** Make the declared dependency real rather than dropping it.
- **F007 (agree on the representation and `uniform`; the categorizer needs your decision).**
  Moving `KNet` and its accessors to `Rep/KnowledgeNet.lean` and keeping one `Dist.uniform` is
  mechanical. Splitting `CatConfig` and turning its two hard-coded models into supplied
  interpretations is a design change to the categorizer. See the decisions below.
- **F008 (agree; more important than "medium" suggests).** EPAM's agreement theorems and its
  general cue theorems are about different definitions, connected by nothing. That is an
  alignment gap between the explanations and the program that runs, which is exactly what
  CogLean claims to prevent. The bridge theorems should come early.
- **F009 (agree).** I'd move `errorsAt` and `learnedOnTrial` to EPAM's postulates, where
  serial anticipation is the experiment, and keep the general attention rule in CogLib.
- **F010 (agree, low).** A general one-hot strength table with its `total ≠ 0` and `Sharp`
  lemmas.
- **F011 (agree on the families; renaming namespaces needs your decision).** Moving the
  MINERVA-style global-matching memory and the strength memory into `CogLib/Memory/` puts
  every family in one place. Renaming the `Cog.Matrix.*` and `Cog.Exp.*` namespaces touches
  many files and the papers' Lean names. I suggest adopting the rule for new code now and
  renaming later.
- **F012 (agree).** The tool fixes I can make without asking:
  - filter compiler-generated names and `rfl` simp lemmas;
  - count definitions as well as theorems in the proof-tree share;
  - classify single-application proofs as relabellings;
  - tighten the promotion rule.

  The three policy additions need your approval:
  - CogLib docstrings cite theories, not packages above CogLib;
  - only CogLib declares `namespace Cog`;
  - a refined promotion rule.

## Decisions pending (for the user)

1. **Approve the policy additions** in F012.
2. **The order of refactoring.** I suggest:
   1. F001 then F002;
   2. F004;
   3. F003 and F005;
   4. F008;
   5. F006 and the mechanical part of F007;
   6. F009 and F010;
   7. F011 (families only).

   Each is its own commit, with all packages rebuilt and the catalog regenerated.
3. **F007's categorizer redesign:** do it, or leave the two models hard-coded with a note.
4. **F011's namespace renaming:** now, later, or never.

When findings are fixed, update their status in `FINDINGS.md` with the commit. The next
audit's review checks each one.
