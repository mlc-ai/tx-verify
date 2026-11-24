-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Dependency
public import Core.Assembly.WaitOrder

@[expose] public section

/-! ## Frames of the order relations at the nodes of an effect-only extension

`Y` differs from `X` in the `rf`, `tensor`, `tensorStores` and `clc` rows only, so `Y.tr`,
`Y.get`, `Y.objects` and `Y.async` are those of `X` definitionally. Every order atom that reads
only those transfers with no hypothesis: `IssueStage`, `Resumes`, `GroupWaitsFor`,
`WaitObserves`, `StageOrder`'s `TracksMma` and `TracksCpAsync`, and `p ∈ GroupWaitStages`. The
rows that do change need one hypothesis each, and these lemmas name them:

* `hpres`: the present rows (`RefPresent`, hence `AsyncPresent` and `IssueStage`) at a node
  outside the new refs `N`;
* `hedge`: the `StageEdge` hop at two old refs. Its clauses read the presence of two stages whose
  part must be cased one slot at a time, and the `cases ... with` alternatives of a stage casing
  cannot be followed by a second one in the same tactic block, so the 27x27 table of part pairs
  is left to the caller (ten lines over the four stage classes);
* `hneeds`: the need rows that a poll's `MbarObserved` contributes to `Needs`;
* `hbase`: `baseCausality`, already framed for every extension form
  (`recordTensorEffects_baseCausality_iff` and its siblings);
* `hcopy`: the byte observation inside `CopyReleaseSync`
  (`tensorByteFrame_tensorObserved` and its siblings).

Each frame is stated so that a site supplies only those rows, and only at the old nodes. -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {K : Kernel} {X : Execution} {N : Ref → Prop}
  {T : EvId → Option TensorCopy.Observation} {S : EvId → Option TensorStore.Observation}
  {C : EvId → Clc.Effects} {R : Ref → Nat → Option Ref}

set_option quotPrecheck false in
local notation "Y" => ({ X with rf := R, tensor := T, tensorStores := S, clc := C } : Execution)

/-- The presence of one stage of the extension at an old node is that of `X`. -/
theorem asyncPresent_frame (hpres : ∀ u, ¬ N u → ((Y).RefPresent u ↔ X.RefPresent u))
    {i : EvId} {p : Part} (hn : ¬ N (.async i p)) :
    (Y).AsyncPresent i p ↔ X.AsyncPresent i p :=
  hpres (.async i p) hn

/-- The stage order of the extension at two old nodes is that of `X`, from the presence row and
the per-part stage hop `hedge`. -/
theorem stageOrder_frame (hpres : ∀ u, ¬ N u → ((Y).RefPresent u ↔ X.RefPresent u))
    (hedge : ∀ e f, ¬ N e → ¬ N f → StageEdge Y e f → StageEdge X e f)
    {u v : Ref × Bool} (hu : ¬ N u.1) (hv : ¬ N v.1) (h : StageOrder Y u v) : StageOrder X u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  simp only [StageOrder] at h ⊢
  rcases h with ⟨rfl, hb, hb', hp⟩ | ⟨hb, hb', hs⟩
  · exact Or.inl ⟨rfl, hb, hb', (hpres _ hu).1 hp⟩
  · exact Or.inr ⟨hb, hb', hedge _ _ hu hv hs⟩

/-- The issue-stage relation of the extension at two old nodes is that of `X`: its only rows are
the presence of the issuing instruction and of the first stage. -/
theorem issueStage_frame (hpres : ∀ u, ¬ N u → ((Y).RefPresent u ↔ X.RefPresent u))
    {e f : Ref} (he : ¬ N e) (hf : ¬ N f) {b b' : Bool} (h : IssueStage Y (e, b) (f, b')) :
    IssueStage X (e, b) (f, b') := by
  obtain ⟨hb, hb', i, p, he', hf', hpr, hap, hm⟩ := h
  refine ⟨hb, hb', i, p, he', hf', (hpres _ (he' ▸ he)).1 hpr, ?_, hm⟩
  exact (asyncPresent_frame hpres (hf' ▸ hf)).1 hap

/-- **The stage-causality frame.** Outside the new refs `N`, the `stageCausality` edges of the
extension are those of `X`, so every path is a path of `X`. -/
theorem stageCausality_frame (hpres : ∀ u, ¬ N u → ((Y).RefPresent u ↔ X.RefPresent u))
    (hedge : ∀ e f, ¬ N e → ¬ N f → StageEdge Y e f → StageEdge X e f)
    (hbase : ∀ i j, baseCausality L Y i j ↔ baseCausality L X i j)
    (hcopy : ∀ n f, CopyReleaseSync L Y n f → CopyReleaseSync L X n f)
    {u v : Ref × Bool} (hu : ¬ N u.1) (hv : ¬ N v.1) (h : stageCausality L Y u v) :
    Relation.TransGen (stageCausality L X) u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  simp only [stageCausality] at h
  rcases h with hs | ⟨hb, hb', i, j, he', hf', hc⟩ | ⟨hb, hb', j, hf', hc⟩
  · exact Relation.TransGen.single (Or.inl (stageOrder_frame hpres hedge hu hv hs))
  · exact Relation.TransGen.single (Or.inr (Or.inl ⟨hb, hb', i, j, he', hf', (hbase i j).1 hc⟩))
  · exact Relation.TransGen.single (Or.inr (Or.inr ⟨hb, hb', j, hf', hcopy e j hc⟩))

/-- **The dependency-step frame.** Outside the new refs `N`, every `DepStep` of the extension is
one of `X`, so every path is a path of `X`. `hneeds` is the only need row that reads a changed
row: a successful poll's `MbarObserved` contributes to `Needs`. -/
theorem depStep_frame (hpres : ∀ u, ¬ N u → ((Y).RefPresent u ↔ X.RefPresent u))
    (hedge : ∀ e f, ¬ N e → ¬ N f → StageEdge Y e f → StageEdge X e f)
    (hneeds : ∀ j, Needs L Y j = Needs L X j)
    {u v : Ref × Bool} (hu : ¬ N u.1) (hv : ¬ N v.1) (h : DepStep L K Y u v) :
    Relation.TransGen (DepStep L K X) u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  simp only [DepStep] at h
  rcases h with hs | hi | ⟨hb, hb', j, hf', hw⟩ | ⟨hb, hb', w, j, he', hf', hr⟩
  · exact Relation.TransGen.single (Or.inl (stageOrder_frame hpres hedge hu hv hs))
  · exact Relation.TransGen.single (Or.inr (Or.inl (issueStage_frame hpres hu hv hi)))
  · obtain ⟨fills, hmem, hpr, hf⟩ := hw
    have hmem' : Need.node fills ∈ Needs L X j := by rw [← hneeds j]; exact hmem
    exact Relation.TransGen.single (Or.inr (Or.inr (Or.inl
      ⟨hb, hb', j, hf', fills, hmem', (hpres e hu).1 hpr, hf⟩)))
  · exact Relation.TransGen.single (Or.inr (Or.inr (Or.inr ⟨hb, hb', w, j, he', hf', hr⟩)))

end
end PTX
