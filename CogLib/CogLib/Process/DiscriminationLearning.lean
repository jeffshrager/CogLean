/-
Processes: discrimination learning in a net.

Learning a code in a discrimination net means finding a unique terminal for
its image, or creating one by growing the net at a point of confusion:
* an empty terminal (the null image) simply receives the new image;
* a terminal holding a *different* image is a point of confusion. The codes
  are scanned in noticing order for a difference, and a test on it is put in
  place of the terminal, with the old image on one side and the new on the
  other;
* nothing else in the net changes.

`learn` adds one test per confusion. `learnK` notices up to `k` differences,
adding redundant tests on the new code's side with null images on the
branches it doesn't take.

Results:
* `learn_recognizes`: after learning a code, the net recognizes it.
* `learn_preserves`: learning one code never disturbs the recognition of
  another. Learning is local.
* `learnAll_recognizes`: a list of mutually noticeable codes is learned with
  one cycle each.
* `learned_test_is_first_noticed_difference`: the test grown is the first
  difference in noticing order.
* As phenomena (`netLearner`): non-interference, learning to criterion, and
  stimulus generalization.
* As a retriever (`netRetriever`): stable retrieval, and agreement on the
  features a probe's path tests (`net_agreesOn`).
-/

import CogLib.Memory.DiscriminationNet
import CogLib.Control.Attention
import CogLib.Phenomena.RetrievalLaws
import CogLib.Phenomena.Learning

namespace Cog

namespace Net

/-- Discrimination learning: discriminate a new code into the net. -/
def learn (order : NoticingOrder) : Net → Item → Net
  | leaf none, x => leaf (some x)
  | leaf (some z), x =>
    if z = x then leaf (some z) else
      match firstDiff order x z with
      | some f =>
        if x.feat f then test f (leaf (some z)) (leaf (some x))
        else test f (leaf (some x)) (leaf (some z))
      | none => leaf (some z)
  | test f n0 n1, x =>
    if x.feat f then test f n0 (n1.learn order x) else test f (n0.learn order x) n1

/-- **Learning succeeds.** If the new code is noticeably different from every
image already stored, after learning it the net recognizes it. -/
theorem learn_recognizes (order : NoticingOrder) (N : Net) (x : Item)
    (hn : ∀ z ∈ N.images, z ≠ x → Noticeable order x z) :
    Recognizes (N.learn order x) x := by
  induction N with
  | leaf img =>
    cases img with
    | none => simp [learn, Recognizes, select]
    | some z =>
      by_cases hzx : z = x
      · subst hzx; simp [learn, Recognizes, select]
      · obtain ⟨f, hf⟩ := hn z (by simp [images]) hzx
        simp only [learn, hzx, ite_false, hf]
        cases hx : x.feat f <;> simp [Recognizes, select, hx]
  | test f n0 n1 ih0 ih1 =>
    cases hx : x.feat f with
    | true =>
      have := ih1 (fun z hz => hn z (by simp [images, hz]))
      simpa [learn, Recognizes, select, hx] using this
    | false =>
      have := ih0 (fun z hz => hn z (by simp [images, hz]))
      simpa [learn, Recognizes, select, hx] using this

/-- **Learning does not interfere.** Learning `x` leaves every other
recognized code recognized. -/
theorem learn_preserves (order : NoticingOrder) (N : Net) (x y : Item)
    (hy : Recognizes N y) (hyx : y ≠ x) : Recognizes (N.learn order x) y := by
  induction N with
  | leaf img =>
    cases img with
    | none => simp [Recognizes, select] at hy
    | some z =>
      have hzy : z = y := by simpa [Recognizes, select] using hy
      subst hzy
      simp only [learn, hyx, ite_false]
      cases hf : firstDiff order x z with
      | none => simp [Recognizes, select]
      | some f =>
        have hd := firstDiff_differs hf
        cases hx : x.feat f <;> cases hz : z.feat f <;>
          simp_all [Recognizes, select]
  | test f n0 n1 ih0 ih1 =>
    unfold Recognizes at ih0 ih1 hy ⊢
    cases hyf : y.feat f <;> cases hxf : x.feat f <;>
      simp_all [learn, select]

theorem images_learn_subset (order : NoticingOrder) (N : Net) (x : Item) :
    ∀ z ∈ (N.learn order x).images, z = x ∨ z ∈ N.images := by
  induction N with
  | leaf img =>
    cases img with
    | none => simp [learn, images]
    | some w =>
      by_cases hw : w = x
      · subst hw; simp [learn, images]
      · simp only [learn, hw, ite_false]
        cases hf : firstDiff order x w with
        | none => simp [images]
        | some f =>
          intro z hz
          cases hxf : x.feat f <;> simp [hxf, images] at hz <;> rcases hz with h | h <;> simp [h, images]
  | test f n0 n1 ih0 ih1 =>
    intro z hz
    cases hx : x.feat f <;> simp only [learn, hx, ite_true, ite_false, Bool.false_eq_true, images,
      List.mem_append] at hz ⊢
    · rcases hz with hz | hz
      · rcases ih0 z hz with h | h <;> simp_all
      · simp_all
    · rcases hz with hz | hz
      · simp_all
      · rcases ih1 z hz with h | h <;> simp_all

/-- Learn a list of codes, one learning cycle each, in order. -/
def learnAll (order : NoticingOrder) (N : Net) (xs : List Item) : Net :=
  xs.foldl (fun n x => n.learn order x) N

theorem learnAll_preserves (order : NoticingOrder) (xs : List Item) :
    ∀ (N : Net) (y : Item), Recognizes N y → y ∉ xs →
      Recognizes (learnAll order N xs) y := by
  induction xs with
  | nil => intro N y h _; simpa [learnAll] using h
  | cons a rest ih =>
    intro N y hy hnot
    simp only [List.mem_cons, not_or] at hnot
    have h1 := learn_preserves order N a y hy hnot.1
    simpa [learnAll] using ih (N.learn order a) y h1 hnot.2

/-- **A list is learned in one cycle per code**, provided any two different
codes involved (already stored, or on the list) are noticeably different. -/
theorem learnAll_recognizes (order : NoticingOrder) (xs : List Item) :
    ∀ (N : Net),
      (∀ x ∈ xs, ∀ z, (z ∈ N.images ∨ z ∈ xs) → z ≠ x → Noticeable order x z) →
      ∀ x ∈ xs, Recognizes (learnAll order N xs) x := by
  induction xs with
  | nil => intro N _ x hx; simp at hx
  | cons a rest ih =>
    intro N H x hx
    have H' : ∀ x ∈ rest, ∀ z, (z ∈ (N.learn order a).images ∨ z ∈ rest) → z ≠ x →
        Noticeable order x z := by
      intro x hx z hz hzx
      apply H x (List.mem_cons_of_mem a hx) z _ hzx
      rcases hz with hz | hz
      · rcases images_learn_subset order N a z hz with h | h
        · subst h; exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem a hz)
    by_cases hr : x ∈ rest
    · simpa [learnAll] using ih (N.learn order a) H' x hr
    · have hxa : x = a := by
        rcases List.mem_cons.mp hx with h | h
        · exact h
        · exact absurd h hr
      subst hxa
      have h1 : Recognizes (N.learn order x) x :=
        learn_recognizes order N x (fun z hz hzx => H x hx z (Or.inl hz) hzx)
      simpa [learnAll] using learnAll_preserves order rest (N.learn order x) x h1 hr

/-- **The test grown at a point of confusion is the first difference in the
noticing order.** -/
theorem learned_test_is_first_noticed_difference (order : NoticingOrder)
    (x z : Item) (f : Feature) (hzx : z ≠ x) (hf : firstDiff order x z = some f) :
    ∃ n0 n1, (leaf (some z)).learn order x = test f n0 n1 := by
  simp only [learn, hzx, ite_false, hf]
  cases x.feat f <;> exact ⟨_, _, rfl⟩

/-- A net is *clean* when each image is stored once and every stored image is
recognized as itself. -/
def Clean (N : Net) : Prop := N.images.Nodup ∧ ∀ z ∈ N.images, N.select z = some z

/-- In a clean net, the images below each branch of a test are clean, and
take that branch. -/
theorem clean_test {f : Feature} {n0 n1 : Net} (h : Clean (test f n0 n1)) :
    Clean n0 ∧ Clean n1 ∧ (∀ z ∈ n0.images, z.feat f = false) ∧
      (∀ z ∈ n1.images, z.feat f = true) := by
  obtain ⟨hnd, hsel⟩ := h
  simp only [images, List.nodup_append] at hnd
  obtain ⟨hnd0, hnd1, hdisj⟩ := hnd
  have side0 : ∀ z ∈ n0.images, z.feat f = false ∧ n0.select z = some z := by
    intro z hz
    have hs := hsel z (by simp [images, hz])
    simp only [select] at hs
    cases hzf : z.feat f
    · simp [hzf] at hs; exact ⟨rfl, hs⟩
    · simp [hzf] at hs
      exact absurd rfl (hdisj z hz z (select_mem_images n1 z z hs))
  have side1 : ∀ z ∈ n1.images, z.feat f = true ∧ n1.select z = some z := by
    intro z hz
    have hs := hsel z (by simp [images, hz])
    simp only [select] at hs
    cases hzf : z.feat f
    · simp [hzf] at hs
      exact absurd rfl (hdisj z (select_mem_images n0 z z hs) z hz)
    · simp [hzf] at hs; exact ⟨rfl, hs⟩
  exact ⟨⟨hnd0, fun z hz => (side0 z hz).2⟩, ⟨hnd1, fun z hz => (side1 z hz).2⟩,
    fun z hz => (side0 z hz).1, fun z hz => (side1 z hz).1⟩

/-- **Learning keeps a net clean.** -/
theorem learn_clean (order : NoticingOrder) (N : Net) (x : Item) (h : Clean N) :
    Clean (N.learn order x) := by
  induction N with
  | leaf img =>
    cases img with
    | none => exact ⟨by simp [learn, images], by simp [learn, images, select]⟩
    | some z =>
      by_cases hzx : z = x
      · simpa [learn, hzx] using h
      · simp only [learn, hzx, ite_false]
        cases hf : firstDiff order x z with
        | none => exact h
        | some f =>
          have hd := firstDiff_differs hf
          have hxz : x ≠ z := Ne.symm hzx
          cases hx : x.feat f <;> cases hz : z.feat f <;> simp_all [Clean, images, select]
  | test f n0 n1 ih0 ih1 =>
    obtain ⟨c0, c1, s0, s1⟩ := clean_test h
    cases hxf : x.feat f with
    | true =>
      simp only [learn, hxf, ite_true]
      have cL := ih1 c1
      refine ⟨?_, ?_⟩
      · simp only [images, List.nodup_append]
        refine ⟨c0.1, cL.1, ?_⟩
        intro w hw w' hw' hww'
        subst hww'
        have h0 := s0 w hw
        rcases images_learn_subset order n1 x w hw' with h' | h'
        · subst h'; rw [hxf] at h0; cases h0
        · rw [s1 w h'] at h0; cases h0
      · intro z hz
        simp only [images, List.mem_append] at hz
        rcases hz with hz | hz
        · simp [select, s0 z hz, c0.2 z hz]
        · have hzf : z.feat f = true := by
            rcases images_learn_subset order n1 x z hz with h' | h'
            · subst h'; exact hxf
            · exact s1 z h'
          simp [select, hzf, cL.2 z hz]
    | false =>
      simp only [learn, hxf, Bool.false_eq_true, ite_false]
      have cL := ih0 c0
      refine ⟨?_, ?_⟩
      · simp only [images, List.nodup_append]
        refine ⟨cL.1, c1.1, ?_⟩
        intro w hw w' hw' hww'
        subst hww'
        have h1 := s1 w hw'
        rcases images_learn_subset order n0 x w hw with h' | h'
        · subst h'; rw [hxf] at h1; cases h1
        · rw [s0 w h'] at h1; cases h1
      · intro z hz
        simp only [images, List.mem_append] at hz
        rcases hz with hz | hz
        · have hzf : z.feat f = false := by
            rcases images_learn_subset order n0 x z hz with h' | h'
            · subst h'; exact hxf
            · exact s0 z h'
          simp [select, hzf, cL.2 z hz]
        · simp [select, s1 z hz, c1.2 z hz]

/-- **Every net EPAM learns from an empty one is clean**: each image is stored
once, and recognized as itself. -/
theorem learnAll_clean (order : NoticingOrder) (xs : List Item) :
    ∀ N, Clean N → Clean (learnAll order N xs) := by
  induction xs with
  | nil => intro N h; simpa [learnAll] using h
  | cons a rest ih =>
    intro N h
    simpa [learnAll] using ih (N.learn order a) (learn_clean order N a h)

theorem clean_empty : Clean (leaf none) := ⟨by simp [images], by simp [images]⟩

/-- Redundant tests on the features `fs`: `x` goes down its own branch of
each, and the other branch gets a null image. -/
def chain : List Feature → Item → Net
  | [], x => leaf (some x)
  | f :: fs, x =>
    if x.feat f then test f (leaf none) (chain fs x) else test f (chain fs x) (leaf none)

/-- Discrimination learning noticing up to `k` differences per confusion,
with redundant tests (`chain`) beyond the first. -/
def learnK (order : NoticingOrder) (k : Nat) : Net → Item → Net
  | leaf none, x => leaf (some x)
  | leaf (some z), x =>
    if z = x then leaf (some z) else
      match diffs order k x z with
      | [] => leaf (some z)
      | f :: fs =>
        if x.feat f then test f (leaf (some z)) (chain fs x)
        else test f (chain fs x) (leaf (some z))
  | test f n0 n1, x =>
    if x.feat f then test f n0 (n1.learnK order k x) else test f (n0.learnK order k x) n1

end Net

/-! ### Discrimination learning as an incremental learner, and its phenomena -/

/-- A discrimination net with one-test learning, as an incremental learner. -/
def netLearner (order : NoticingOrder) : IncrementalLearner Net Item :=
  ⟨fun N x => N.learn order x, Net.select⟩

/-- **Discrimination learning has non-interference.** -/
theorem netLearner_nonInterference (order : NoticingOrder) :
    Phenomena.NonInterference (netLearner order) :=
  fun N x y hy hyx => Net.learn_preserves order N x y hy hyx

/-- The lists a discrimination learner can learn: any two different items
are noticeably different under its noticing order. -/
def PairwiseNoticeable (order : NoticingOrder) (xs : List Item) : Prop :=
  ∀ x ∈ xs, ∀ z ∈ xs, z ≠ x → Noticeable order x z

/-- **Discrimination learning reaches criterion** from an empty memory, on
every list of pairwise noticeable items. Proved from the general
`criterion_of_nonInterference`: the invariant is "every stored image is on
the list". -/
theorem netLearner_reachesCriterion (order : NoticingOrder) :
    Phenomena.ReachesCriterion (netLearner order) (Net.leaf none) (PairwiseNoticeable order) := by
  apply Phenomena.criterion_of_nonInterference _ (netLearner_nonInterference order)
  intro xs hxs
  refine ⟨fun N => ∀ z ∈ N.images, z ∈ xs, by simp [Net.images], ?_, ?_⟩
  · intro N x hx hN z hz
    rcases Net.images_learn_subset order N x z hz with h | h
    · exact h ▸ hx
    · exact hN z h
  · intro N x hx hN
    exact Net.learn_recognizes order N x (fun z hz hzx => hxs x hx z (hN z hz) hzx)

/-- **Discrimination nets generalize.** A learned code `x`, and a different
code `y` that agrees with it on every feature its path examines: `y` is
recognized as `x`. -/
theorem netLearner_generalizes (order : NoticingOrder) (N : Net) (x y : Item)
    (hyx : y ≠ x) (hx : Net.Recognizes N x) (hagree : ∀ f ∈ N.path x, x.feat f = y.feat f) :
    Phenomena.StimulusGeneralization (netLearner order) N x y := by
  refine ⟨hyx, hx, ?_⟩
  show N.select y = some x
  rw [Net.select_depends_only_on_noticed_features N x y hagree]
  exact hx

/-! ### Discrimination nets as retrievers -/

/-- What a net's probe calls up: the image it sorts to, for certain. -/
def Net.retrieve (N : Net) : Item → Dist (Option Item) := fun y => Dist.pure (N.select y)

/-- A discrimination net with one-test learning, as a retriever. -/
def netRetriever (order : NoticingOrder) : Retriever Net Item := (netLearner order).toRetriever

theorem netRetriever_retrieve (order : NoticingOrder) (N : Net) :
    (netRetriever order).retrieve N = N.retrieve := rfl

/-- **Discrimination learning has stable retrieval.** -/
theorem netRetriever_stableRetrieval (order : NoticingOrder) :
    Phenomena.StableRetrieval (netRetriever order) :=
  Phenomena.stableRetrieval_of_nonInterference _ (netLearner_nonInterference order)

/-- **A net agrees on the features a path tests.** If each image is stored
once, and `x` is recognized as the stored image `y`, which the net itself
recognizes, then whatever `x` calls up agrees with it on every feature in
`fs`, when `fs` lies on `x`'s path. -/
theorem net_agreesOn (N : Net) (x y : Item) (fs : List Feature) (hnd : N.images.Nodup)
    (hy : N.select y = some y) (hx : N.select x = some y) (hcover : ∀ f ∈ fs, f ∈ N.path x) :
    Phenomena.AgreesOn N.retrieve x fs := by
  intro y' hy' f hf
  have h' : some y' = N.select x := Dist.possible_pure.mp hy'
  rw [hx] at h'
  cases h'
  exact Net.confusion_agrees_on_path N x y hnd hy hx f (hcover f hf)

/-- **A discrimination net retrieves deterministically.** -/
theorem netRetriever_deterministic (order : NoticingOrder) :
    Laws.Deterministic (netRetriever order) :=
  fun N x => ⟨N.select x, rfl⟩

theorem Net.retrieve_of_select (N : Net) (x : Item) (r : Option Item) (h : N.select x = r) :
    N.retrieve x = Dist.pure r := by
  rw [← h]; rfl

theorem Net.possible_retrieve (N : Net) (x y : Item) (hx : N.select x = some y) :
    (N.retrieve x).Possible (some y) :=
  Dist.possible_pure.mpr (by simp [hx])

end Cog
