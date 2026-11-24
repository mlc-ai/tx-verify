-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaFinishConsistent
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Tcgen05.TcReadSemanticFrame

@[expose] public section

/-! Once operands were read, arithmetic completion changes no memory observation. -/
namespace PTX
open AsyncCopy
noncomputable section

def Execution.completeMma (X : Execution) (i : EvId) : Execution :=
  { X with async := { X.async with mmaDone := fun j => if j = i then true else X.async.mmaDone j } }

theorem completeMma_eq_finish {X : Execution} {i : EvId} {values : MmaOperands}
    (hv : X.async.mmaOperands i = some values) :
    X.completeMma i = X.finishMma i values (fun k => X.rf (.async i (.mmaRead false k)) 0)
      (fun k => X.rf (.async i (.mmaRead true k)) 0) := by
  have hvals : (fun j => if j = i then some values else X.async.mmaOperands j) =
      X.async.mmaOperands := by
    funext j
    by_cases h : j = i
    · subst j; simp [hv]
    · simp [h]
  have hrf : (X.finishMma i values (fun k => X.rf (.async i (.mmaRead false k)) 0)
      (fun k => X.rf (.async i (.mmaRead true k)) 0)).rf = X.rf := by
    funext e offset
    cases e with
    | thread j => rfl
    | async j p =>
      cases p <;> try rfl
      case mmaRead isB k =>
        simp only [Execution.finishMma]
        split_ifs with h hB
        · obtain ⟨rfl, rfl⟩ := h; subst hB; rfl
        · obtain ⟨rfl, rfl⟩ := h; simp only [Bool.not_eq_true] at hB; subst hB; rfl
        · rfl
  unfold Execution.completeMma Execution.finishMma
  change _ = { X with rf := _, async := { X.async with mmaOperands := _, mmaDone := _ } }
  rw [hvals]
  change _ = { X with rf := (X.finishMma i values _ _).rf, async := _ }
  rw [hrf]

theorem Execution.le_completeMma (X : Execution) (i : EvId) : X.le (X.completeMma i) := by
  refine ⟨fun _ => List.prefix_refl _, fun _ _ _ => rfl, ?_, (Execution.le_refl X).2.2.2⟩
  refine ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ _ h => h, ?_, fun _ h => h,
    fun _ _ _ h => h, fun _ _ _ h => h⟩
  intro j hj
  by_cases he : j = i
  · simp [completeMma, he]
  · simpa [completeMma, he] using hj

/-- Arithmetic completion changes none of the facts that the tcgen05 read obligations read. -/
theorem completeMma_semanticFrame {L : Launch} {X : Execution} {i : EvId} :
    TcMma.SemanticFrame L X (X.completeMma i) :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl⟩

theorem completeMma_readOk {L : Launch} {A : List Assumption} {X : Execution} {i : EvId}
    (h : TcMma.ReadOk L A X) : TcMma.ReadOk L A (X.completeMma i) :=
  completeMma_semanticFrame.readOk.mpr h

/-- An MMA completion is no memory access, covers no byte and observes nothing, so the model
causality is that of `X`. -/
theorem completeMma_modelCausality {L : Launch} {X : Execution} {i : EvId}
    {l : Loc} {a b : Ref} : modelCausality L
        (X.completeMma i) l a b ↔ modelCausality L X l a b := by
  have hgroup : ∀ (j : EvId) (k : GroupWait),
      (∀ q ∈ GroupWaitStages (X.completeMma i) j k, (X.completeMma i).AsyncPresent j q) ↔
        ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q := fun j k =>
    forall₂_congr fun q hq => by
      rcases groupWaitStages_cases X j k hq with rfl | rfl | rfl | rfl <;> exact Iff.rfl
  have hfin : ∀ j p w, AsyncFinished L (X.completeMma i) j p w ↔ AsyncFinished L X j p w :=
    fun j p w => or_congr (exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      hgroup j k) Iff.rfl
  have honly : ∀ j p w, AsyncOnlyFinished (X.completeMma i) j p w ↔ AsyncOnlyFinished X j p w :=
    fun j p w => and_congr_right fun _ => and_congr_right fun _ => hgroup j _
  cases a <;> cases b
  · exact Iff.rfl
  · exact Iff.rfl
  · exact and_congr_right fun _ => exists_congr fun w => and_congr_left' (hfin _ _ w)
  · refine and_congr_right fun _ => ?_
    apply AsyncChain.congr_on_edges (L := L) (X := X.completeMma i) (Y := X)
      (fun _ _ => AsyncBefore.congr (X := X.completeMma i) (Y := X) (fun _ _ => Iff.rfl) hfin
        honly (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl))
    rintro ⟨j,p⟩ b edge
    cases p <;> first
      | exact Iff.rfl
      | (obtain ⟨acc,w,hi,_⟩ := edge.1; cases hi.2)

theorem consistent_completeMma {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId}
    (hX : Consistent L K A mem0 X) (hs : X.async.mmaStarted i = true)
    (hn : X.async.mmaDone i = false) (hready : TcMma.CompletionReady L X i)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.completeMma i)) :
    Consistent L K A mem0 (X.completeMma i) := by
  obtain ⟨values, hv⟩ : ∃ values, X.async.mmaOperands i = some values := by
    cases hh : X.async.mmaOperands i with
    | none => simp [Snapshot.mmaStarted,hh] at hs
    | some values => exact ⟨values,rfl⟩
  have hobj : AsyncCopy.ObjectsOk X := hX.tma.2.2.1
  have hfr : SinkFrame L K A X (X.completeMma i) (fun n => MmaRef i n.1) := by
    rw [completeMma_eq_finish hv]
    exact finishMma_sinkFrame hobj hX.tcCommit hn hX.orderOk
  have horder := hfr.orderOk hX.orderOk
  have hneeds : ∀ e, Needs L (X.completeMma i) e = Needs L X e := by
    intro e
    rw [completeMma_eq_finish hv]
    exact finishMma_needs hobj e
  have hpres : ∀ x, ¬ MmaRef i x → X.RefPresent x → (X.completeMma i).RefPresent x := by
    intro x hx h
    rw [completeMma_eq_finish hv]
    exact (finishMma_present_old hx).mpr h
  exact {
    thr := hX.thr
    outside := hX.outside
    rf := hX.rf
    ctaBar := hX.ctaBar
    cluster := hX.cluster
    dependency := by
      refine ⟨?_, fun o ho => hfr.toBase.depAcyclic hX.dependency.acyclic o ho⟩
      intro e hret n hn'
      rw [hneeds] at hn'
      have hready := hX.dependency.ready e hret n hn'
      cases n with
      | cond holds => exact hready
      | node fills =>
        obtain ⟨x, hx, hf⟩ := hready
        have hno : ¬ MmaRef i x := fun ⟨p, he, hp⟩ => needs_node_not_mma hobj hn' hp (he ▸ hf)
        exact ⟨x, hpres x hno hx, hf⟩
    shfl := hX.shfl
    vote := hX.vote
    warpValue := hX.warpValue
    matrix := hX.matrix
    elect := hX.elect
    warpBar := hX.warpBar
    observation := horder.observation
    object := horder.object
    asyncObject := horder.asyncObject
    initFence := horder.initFence
    noFuture := hX.noFuture.of_frame (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context (X := X) (Y := X.completeMma i) rfl rfl
        (fun h => completeMma_modelCausality.mp h) (fun h => h))
    hidden := hX.hidden.of_frame (fun _ _ _ h => h) (fun _ _ _ h => h) rfl
      (fun _ _ _ => ByteCausality.of_same_context (X := X) (Y := X.completeMma i) rfl rfl
        (fun h => completeMma_modelCausality.mp h) (fun h => h))
    tma := by
      refine ⟨hX.tma.1, ⟨hX.tma.2.1.1, ?_⟩, hX.tma.2.2⟩
      intro j hj
      by_cases he : j = i
      · subst j; exact hs
      · exact hX.tma.2.1.2 j (by simpa [Execution.completeMma,he] using hj)
    clc := hX.clc
    tensor := hX.tensor
    store := hX.store
    reduce := hX.reduce.of_tensorStores rfl fun _ _ _ _ hc _ _ => ⟨hc, rfl⟩
    atomic := atomicOk_congr (X := X) (Y := X.completeMma i)
      (fun p l n => by cases p <;> exact Iff.rfl) (fun _ _ => Iff.rfl)
      (fun p k => by cases p <;> rfl) hX.atomic
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, hX.fenceSc.causal⟩
    tmemPair := hX.tmemPair
    tcCommit := by
      intro c rank hc
      obtain ⟨hcommit, hd⟩ := hX.tcCommit c rank hc
      refine ⟨hcommit, ?_⟩
      intro mma hm
      have hh := hd mma hm
      change (if mma = i then true else X.async.mmaDone mma) = true
      split <;> simp_all
    tmemPairCompletion := Tmem.Pair.completionClosed_of_trace rfl rfl rfl hX.tmemPairCompletion
    tmemPairResult := hX.tmemPairResult
    mmaCompletion := TcMma.completionClosed_update
      (X := X) (Y := X.completeMma i) (i := i) (fun _ _ _ _ _ => Iff.rfl)
      (fun _ => rfl) hX.mmaCompletion hready
    tcRead := completeMma_readOk hX.tcRead
    asm := hasm }

theorem completeMma_size {L : Launch} {X : Execution} {i : EvId} {values : MmaOperands}
    (hv : X.async.mmaOperands i = some values) (hg : i.1 < L.threads)
    (hi : i.2 < (X.tr i.1).length) (hn : X.async.mmaDone i = false) :
    X.size L < (X.completeMma i).size L := by
  rw [completeMma_eq_finish hv]
  exact finishMma_size hg hi hn

/-- Any maximal execution with recorded MMA operands also contains that MMA's
arithmetic completion. This is a consequence of the model for every kernel. -/
theorem Maximal.mma_done_of_started {L : Launch} {K : Kernel} {mem0 : Mem0}
    {X : Execution} {i : EvId} (hm : Maximal L K [] mem0 X)
    (hs : X.async.mmaStarted i = true) (hready : TcMma.CompletionReady L X i) :
    X.async.mmaDone i = true := by
  classical
  cases hn : X.async.mmaDone i with
  | true => rfl
  | false =>
    have hv : ∃ values, X.async.mmaOperands i = some values := by
      cases hh : X.async.mmaOperands i with
      | none => simp [Snapshot.mmaStarted,hh] at hs
      | some values => exact ⟨values,rfl⟩
    obtain ⟨values,hv⟩ := hv
    have hi : ∃ ev, X.get i = some ev := by
      rcases hm.1.tma.2.1.1 i hs with ⟨d,s,accum,mask,operands,⟨pc,hi⟩,_⟩ |
        ⟨c,operands,⟨pc,hi⟩,_⟩ | ⟨s,operands,⟨pc,hi⟩,_⟩
      · exact ⟨_,hi⟩
      · exact ⟨_,hi⟩
      · exact ⟨_,hi⟩
    obtain ⟨ev,hi⟩ := hi
    have hlen := len_of_get hi
    have hg : i.1 < L.threads := by
      by_contra hh
      rw [hm.1.outside i.1 (by omega)] at hlen
      simp at hlen
    have hc := consistent_completeMma hm.1 hs hn hready (by simp)
    have hle := hm.2 _ hc (X.le_completeMma i)
    have hlt := completeMma_size hv hg hlen hn
    omega


end
end PTX
