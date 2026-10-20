# A multi-level theorem, narrated: learning to criterion

This note walks through one theorem of the EPAM theory, `Epam.Phenomena.learning_to_criterion`, and the chain of lemmas it rests on. It is the deepest dependency chain in CogLean so far. It runs through three layers of the library (a theory-neutral phenomenon, a general process, a memory structure) down to Lean's core, and it also says something substantive about the theory.

## The claim

> If every two items on a list are *noticeably different* (the noticing order can find some feature on which they differ), then learning the list with one discrimination cycle (F1) per item, starting from an empty memory, leaves **every item recognized**.

In psychological terms, discrimination learning reaches criterion, and **learning later items never undoes the recognition of earlier ones**.

```lean
-- EPAM/Epam/Phenomena.lean
theorem learning_to_criterion (order : NoticingOrder) :
    Cog.Phenomena.ReachesCriterion (learner order) (leaf none) (PairwiseNoticeable order)
```

`ReachesCriterion` is CogLib's theory-neutral statement of the phenomenon. It mentions no nets and no features, only a learner that can *study* a stimulus and *recognize* one:

```lean
-- CogLib/CogLib/Phenomena/Learning.lean
def ReachesCriterion (L : IncrementalLearner State Stim) (s0 : State)
    (Learnable : List Stim → Prop) : Prop :=
  ∀ xs, Learnable xs → ∀ x ∈ xs, L.Recognizes (L.studyAll s0 xs) x
```

EPAM's learner (`learner order`) is a discrimination net: study is F1 and recognition is D2. The rest of the vocabulary is CogLib's:

- **`Item`:** a stimulus code, a list of bits (`Rep/Features`).
- **`Net`:** a discrimination net of testing points and terminals (`Memory/DiscriminationNet`).
- **`Recognizes N x`:** sorting `x` through `N` reaches a terminal holding `x`'s own image.
- **`learn order N x`:** one F1 cycle (`Process/DiscriminationLearning`). It sorts `x` down the net. If `x` lands on a terminal holding a different image (the point of confusion), F1 replaces that terminal with a test on the first feature, in noticing order, where the two differ.
- **`firstDiff order x z`:** the first feature, in noticing order, on which `x` and `z` differ, if any (`Control/Attention`).
- **`Noticeable order x z`:** `firstDiff` finds such a feature. `PairwiseNoticeable order xs`: every two different items of `xs` are noticeable.

## The dependency tree

```
learning_to_criterion                  (EPAM)                       the phenomenon, for EPAM
└── netLearner_reachesCriterion        (Process/DiscriminationLearning)
    ├── criterion_of_nonInterference   (Phenomena/Learning)          for any learner
    │   └── studyAll_recognizes
    │       └── studyAll_preserves        later study keeps old items
    ├── netLearner_nonInterference        a discrimination net has non-interference
    │   └── learn_preserves               one F1 cycle keeps old items   <- the crux
    │       └── firstDiff_differs         a noticed difference is a real difference
    │           └── List.find?_some       (Lean's core library)
    ├── learn_recognizes                  F1 succeeds on the new item
    └── images_learn_subset               F1 stores nothing unexpected
```

The left branch knows nothing about nets: it holds for every learner. The right branches are about discrimination nets, and nothing in them is specific to EPAM either. EPAM's own contribution is the choice of mechanism.

## Level by level, from the bottom up

### Level 1: `firstDiff_differs`: a noticed difference is a real difference

```lean
theorem firstDiff_differs {order : NoticingOrder} {x z : Item} {f : Feature}
    (h : firstDiff order x z = some f) : x.feat f ≠ z.feat f
```

F1 scans features in noticing order and stops at the first one where the new item and the stored image differ. This lemma confirms that what it found really is a difference. It is one step from Lean's own fact about `List.find?`. It sounds trivial, but everything above depends on it: a test grown on that feature *will* send the two items down different branches.

### Level 2: `learn_preserves`, the crux: one learning cycle doesn't interfere

```lean
theorem learn_preserves (order : NoticingOrder) (N : Net) (x y : Item)
    (hy : Recognizes N y) (hyx : y ≠ x) : Recognizes (N.learn order x) y
```

If `y` is already recognized, learning a different item `x` leaves `y` recognized. The proof is by induction on the net, and it captures one cognitive idea, **locality**: F1 changes the net only at the terminal where `x` lands.

- **At a testing point:** if `x` and `y` take different branches, F1 never touches `y`'s subtree. If they take the same branch, the induction hypothesis applies.
- **At the terminal holding `y`:** if `x` lands there, this is the point of confusion. F1 replaces the terminal with a test on the first noticed difference, putting `y`'s image on one side and `x`'s on the other. By Level 1, `x` and `y` really do differ there, so `y` follows its own branch to its own image.

Restated in the theory-neutral vocabulary, this is `netLearner_nonInterference`: a discrimination net has the property `Cog.Phenomena.NonInterference`.

### Level 2, alongside: `learn_recognizes` and `images_learn_subset`

```lean
theorem learn_recognizes (order : NoticingOrder) (N : Net) (x : Item)
    (hn : ∀ z ∈ N.images, z ≠ x → Noticeable order x z) :
    Recognizes (N.learn order x) x

theorem images_learn_subset (order : NoticingOrder) (N : Net) (x : Item) :
    ∀ z ∈ (N.learn order x).images, z = x ∨ z ∈ N.images
```

- **`learn_recognizes` (F1 succeeds).** After learning `x`, `x` is recognized, provided it is noticeably different from every image already stored. If it weren't, F1 would find no difference and the confusion would remain.
- **`images_learn_subset` (bookkeeping, but essential).** After learning `x`, the net holds the old images plus `x`, and nothing else.

### Level 3: the general theorem: non-interference ⇒ criterion, for any learner

```lean
theorem studyAll_preserves (L : IncrementalLearner State Stim) (hni : NonInterference L) :
    ∀ (xs : List Stim) (s : State) (y : Stim),
      L.Recognizes s y → y ∉ xs → L.Recognizes (L.studyAll s xs) y

theorem studyAll_recognizes (L : IncrementalLearner State Stim) (hni : NonInterference L)
    (Inv : State → Prop) (xs : List Stim)
    (hinv : ∀ s x, x ∈ xs → Inv s → Inv (L.study s x))
    (hsucc : ∀ s x, x ∈ xs → Inv s → L.Recognizes (L.study s x) x) :
    ∀ s, Inv s → ∀ x ∈ xs, L.Recognizes (L.studyAll s xs) x
```

These are about an arbitrary `IncrementalLearner`, with no nets in sight:

- **`studyAll_preserves`:** with non-interference, a recognized stimulus stays recognized through the study of any list of other stimuli. A plain induction over the list.
- **`studyAll_recognizes`:** suppose some invariant of the learner's state is kept by each study, and while it holds, studying an item makes it recognized. Then one pass through the list leaves every item recognized. For the item just studied: success gives recognition now, and `studyAll_preserves` keeps it to the end. An item that comes up again later in the list is covered by the induction.

`criterion_of_nonInterference` packages this as a phenomenon: non-interference, plus a suitable invariant for each learnable list, gives `ReachesCriterion`.

### Level 4: `netLearner_reachesCriterion`: discrimination nets reach criterion

To use the general theorem, the discrimination net has to supply its three ingredients:

- **non-interference:** `netLearner_nonInterference` (Level 2);
- **the invariant:** "every image stored in the net is on the list". It holds for the empty net, and `images_learn_subset` shows each F1 cycle keeps it;
- **success:** while the invariant holds, every stored image is a list item. The list is pairwise noticeable, so `learn_recognizes` applies.

### Level 5: `learning_to_criterion`: the phenomenon, for EPAM

EPAM's learner *is* the discrimination-net learner, so the theorem is Level 4 applied to it. The proof is one line.

## What the proof teaches about the theory

1. **The hypothesis is the content.** The theorem needs the items to be noticeably different *under the noticing order*. Two items that differ only in features the learner never scans can never be told apart, however long it studies. The proof makes "learnable" precise: learnability is relative to what the learner attends to.

2. **Discrimination never forgets, in this theory.** Levels 2 and 3 say the net is *monotone*: what has been recognized stays recognized. So where does forgetting come from? The theorems in CogLib's `Process/Association` give the answer: **from the cues, not the net.**
   - `cue_can_fail_after_growth` (EPAM's `oscillation`) shows that a cue formed when the net was small can become insufficient as the net grows underneath it. A correct response can then fail, and later succeed again.
   - `learning_can_capture_old_cue` (EPAM's `retroactive_inhibition`) shows the same for old material when new material is learned.

   Taken together, the theory puts interference in *retrieval*, not in *storage*. This is a substantive commitment, and it is where theories differ: an activation-based theory such as ACT-R locates interference in activation spread across many associations (the fan effect). Stating both against shared definitions of *cue* and *interference* is what the library is for.

3. **The argument is general, and now it is stated generally.** The chain "local change ⇒ non-interference ⇒ criterion" is `criterion_of_nonInterference`, proved once for every learner. Any other theory whose learning is non-interfering gets learning to criterion by supplying its own non-interference proof and invariant, exactly as the discrimination net does at Level 4. A theory that *lacks* non-interference would need another route, or would provably fail to reach criterion. Either way, the comparison is made on shared ground.

## Checking it

```sh
cd EPAM && lake build
```

Every theorem above is proved, with no `sorry`. `#print axioms Epam.Phenomena.learning_to_criterion` lists `propext`, `Classical.choice` and `Quot.sound`, Lean's standard axioms. `Classical.choice` comes in through a case split in `studyAll_recognizes`.
