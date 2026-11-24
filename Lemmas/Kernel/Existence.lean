-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Kernel.Correct
public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.CtaBarrier.CtaBarrierExecution
public import Lemmas.Async.AsyncOrder
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Execution.NoTma
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Extension.Linear
public import Lemmas.Order.Order

@[expose] public section

/-! # Non-vacuity of the correctness obligations

These are consequences, not new execution rules: any consistent prefix of a correct kernel has a
complete consistent extension. Empty-prefix consistency only needs the optional assumptions to admit
the empty execution. -/

namespace PTX
noncomputable section

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

/-- The local and memory rules admit the empty execution for every program. -/
theorem consistent_empty (hl : L.clusterGridValid)
    (hA : ∀ a ∈ A, a.wf L mem0 Execution.empty) :
    Consistent L K A mem0 Execution.empty := by
  have hT : Execution.empty.NoTma := by
    intro e pc k h; simp [Execution.get, Execution.empty] at h
  have he : Execution.NoTma.EmptyAsync Execution.empty :=
    ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, (fun _ => rfl), fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  have ht := hT.tmaOk he
  have hclc : ClcOk L Execution.empty := by
    refine ⟨Relation.ReflTransGen.refl, ?_⟩
    simp [Execution.empty, Clc.initial, Execution.ClcIssue, Execution.get]
  have hpair : Tmem.Pair.HistoriesOk L Execution.empty := by
    simp [Tmem.Pair.HistoriesOk, Tmem.Pair.RequestHistory, Tmem.Pair.runRequests, Execution.empty]
  have hTensor : TensorOk L Execution.empty := by simp [TensorOk, Execution.empty]
  have hStore : TensorStoreOk L Execution.empty := by simp [TensorStoreOk, Execution.empty]
  have hMulti : AsyncCopy.CommitOk Execution.empty := by simp [AsyncCopy.CommitOk, Execution.empty]
  have heffects : EffectValidity L Execution.empty := ⟨ht, hTensor, hStore, hclc, hpair, hMulti⟩
  have nowaits : ∀ u v, Relation.TransGen (Waits L Execution.empty) u v → False := by
    intro u v path
    obtain ⟨w, edge, _⟩ := Relation.TransGen.head'_iff.mp path
    exact Execution.empty_no_ref u.1 (waits_present heffects edge).1
  have syncObject : ∀ {o : OrderObject} {a c : AsyncCopy.Ref × Bool},
      SyncObjectOrder L Execution.empty o a c → ObjectOrder L Execution.empty o a c := by
    intro o a c h
    cases o with
    | mbar m => exact h.1
    | ctaBar c id => exact h
    | cluster c => exact h
    | tmem cta => exact h
  have noRmw := fun p l n => show ¬ Execution.empty.RmwAt p l n from by
    cases p with
    | thread e =>
      rintro ⟨a, old, new, h, -⟩
      simp [Execution.Rmw, Execution.get, Execution.empty] at h
    | tensor i x y =>
      rintro ⟨fp, hred, -⟩
      obtain ⟨o, red, loc, ho, -⟩ := hred
      simp [Execution.empty] at ho
    | copy i j =>
      rintro ⟨s, r, a, hc, -⟩
      obtain ⟨pc, hc⟩ := hc
      simp [Execution.get, Execution.empty] at hc
  have noScStrong : ∀ e f, ¬ ScStrong L Execution.empty e f := by
    rintro e f ⟨s, s', h, -⟩
    simp [Execution.ThreadFence, Execution.get, Execution.empty] at h
  refine {
    thr := fun g hg => ⟨some {}, .nil _⟩
    outside := fun _ _ => rfl
    rf := ?_
    ctaBar := CtaBarHistoryOk.empty L
    cluster := ClusterHistoryOk.empty L hl
    dependency := {
      ready := fun e hret => by simp [Returned, Execution.get, Execution.empty] at hret
      acyclic := by
        intro o _ n path
        obtain ⟨w, edge, _⟩ := Relation.TransGen.head'_iff.mp path
        rcases edge with edge | edge
        · exact nowaits _ _ (DepStep.waits edge)
        · exact nowaits _ _ (.single (ObjectOrder.waits edge)) }
    shfl := ?_
    vote := ?_
    warpValue := ⟨fun _ _ _ _ _ _ _ _ h _ => by simp [Execution.get, Execution.empty] at h,
      fun _ _ _ _ _ _ _ _ _ h _ => by simp [Execution.get, Execution.empty] at h,
      fun _ _ _ _ _ _ _ _ _ _ h _ => by simp [Execution.get, Execution.empty] at h,
      fun _ _ _ _ h => by simp [Execution.get, Execution.empty] at h⟩
    matrix := ?_
    elect := ?_
    warpBar := ?_
    observation := fun x w ho _ => nowaits _ _ (SyncObserved.waits ho)
    object := by
      intro o n path
      obtain ⟨w, edge, _⟩ := Relation.TransGen.head'_iff.mp path
      rcases edge with edge | edge
      · exact nowaits _ _ (stageCausality.waits edge)
      · exact nowaits _ _ (.single (ObjectOrder.waits (syncObject edge)))
    asyncObject := fun m i p y hb => by simp [MBarrier.Before, Execution.empty] at hb
    initFence := fun m init w y _ _ hb => by simp [MBarrier.Before, Execution.empty] at hb
    noFuture := ?_
    hidden := ?_
    tma := ht
    clc := hclc
    tensor := hTensor
    store := hStore
    reduce := TensorStore.ReduceOk.of_none (fun _ _ h => by simp [Execution.empty] at h)
      (fun _ _ h => by obtain ⟨pc, hp⟩ := h; simp [Execution.get, Execution.empty] at hp)
    atomic := {
      unique := fun p q l n k hp => absurd hp (noRmw p l n)
      acyclic := by
        intro p path
        obtain ⟨q, edge, -⟩ := Relation.TransGen.head'_iff.mp path
        obtain ⟨l, n, hp, -⟩ := edge
        exact noRmw p l n hp }
    fenceSc := {
      total := fun e f hs => absurd hs (noScStrong e f)
      acyclic := fun e path => by
        obtain ⟨w, edge, -⟩ := Relation.TransGen.head'_iff.mp path
        exact noScStrong e w edge.1
      causal := fun e f hs => absurd hs (noScStrong e f) }
    tmemPair := hpair
    tmemPairCompletion :=
      fun ws hws => by rcases hws with ⟨_, _, h, _⟩ | ⟨_, h, _⟩ <;> simp [Execution.empty] at h
    tmemPairResult := hT.noTc.pairResult
    tcCommit := hMulti
    mmaCompletion := by
      intro i j hp hd
      obtain ⟨-,-,-,d,si,ai,mask,-,-,-,-,⟨pc,he⟩,-⟩ := hp
      simp [Execution.get,Execution.empty] at he
    tcRead := ?_
    asm := hA }
  · intro e a bs h
    exact False.elim (Execution.empty_no_memReads e a bs h)
  · intro g i n pc mode a b c recv ok h _
    simp [Execution.get, Execution.empty] at h
  · intro g i n pc mask a ballot h _
    simp [Execution.get, Execution.empty] at h
  · intro g i pc op own recv n h _
    simp [Execution.get, Execution.empty] at h
  · simp [ElectOk, Execution.Elect, Execution.get, Execution.empty]
  · simp [WarpBarOk, Execution.WarpBar, Execution.get, Execution.empty]
  · intro e a bs k w h
    exact False.elim (Execution.empty_no_memReads e a bs h)
  · intro e a bs k w a' bs' h
    exact False.elim (Execution.empty_no_memReads e a bs h)
  · simp [TcMma.ReadOk, TcMma.LoadReadOk, TcMma.AReadOk, Execution.TLd, Execution.MmaIssue,
      Execution.get, Execution.empty]

/-- A bounded, nonempty collection of consistent extensions has a greatest counted
size. This is a finite bound on natural numbers, not a finiteness assumption on values,
poll counts, or the set of executions. -/
theorem bounded_largest_extension
    (hbound : ∃ N, ∀ X, Consistent L K A mem0 X → X.size L ≤ N)
    {X : Execution} (hX : Consistent L K A mem0 X) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧
      ∀ Z, Consistent L K A mem0 Z → X.le Z → Z.size L ≤ Y.size L := by
  classical
  obtain ⟨N, hN⟩ := hbound
  let P : Nat → Prop := fun n => ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ Y.size L = n
  have hP : P (X.size L) := ⟨X, hX, X.le_refl, rfl⟩
  obtain ⟨Y, hY, hXY, hsize⟩ := Nat.findGreatest_spec (hN X hX) hP
  refine ⟨Y, hY, hXY, ?_⟩
  intro Z hZ hXZ
  have hz : P (Z.size L) := ⟨Z, hZ, hXZ, rfl⟩
  have := Nat.le_findGreatest (hN Z hZ) hz
  omega

/-- Bounded size and progress imply that every consistent prefix has a completed
extension. No fairness or eventual-completion hypothesis is assumed for this existence
statement. -/
theorem Correct.complete_extension {post : FinalMem → Prop} (hc : Correct K A L mem0 post)
    (hv : L.Valid K) {X : Execution} (hX : Consistent L K A mem0 X) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ Complete L Y := by
  obtain ⟨Y, hY, hXY, hmax⟩ := bounded_largest_extension (hc.terminates hv) hX
  exact ⟨Y, hY, hXY, hc.progress hv Y ⟨hY,
    fun Z hZ hYZ => hmax Z hZ (Execution.le_trans hXY hYZ)⟩⟩

/-- Every execution has a coherence order (CORRECT-FINAL): a linear extension of the edges of
`CoBefore` whose reverse is not in `CoBefore`, which form a strict partial order. -/
theorem coOrder_exists (X : Execution) : ∃ co, CoOrder L X co := by
  classical
  let r : AsyncCopy.Ref → AsyncCopy.Ref → Prop := fun u v =>
    u = v ∨ (CoBefore L X u v ∧ ¬ CoBefore L X v u)
  have hr : IsPartialOrder AsyncCopy.Ref r :=
    { refl := fun _ => .inl rfl
      trans := by
        rintro u v w (rfl | ⟨huv, hvu⟩) (rfl | ⟨hvw, hwv⟩)
        · exact .inl rfl
        · exact .inr ⟨hvw, hwv⟩
        · exact .inr ⟨huv, hvu⟩
        · exact .inr ⟨huv.trans hvw, fun hwu => hvu (hvw.trans hwu)⟩
      antisymm := by
        rintro u v (rfl | ⟨huv, hvu⟩) (h | ⟨hvu', -⟩)
        · rfl
        · rfl
        · exact h.symm
        · exact absurd hvu' hvu }
  obtain ⟨s, hs, hrs⟩ := extend_partialOrder r
  refine ⟨fun u v => s u v ∧ u ≠ v, ⟨fun w h => h.2 rfl, ?_, ?_, ?_⟩⟩
  · rintro u v w ⟨huv, hne⟩ ⟨hvw, -⟩
    refine ⟨hs.trans _ _ _ huv hvw, ?_⟩
    rintro rfl
    exact hne (hs.antisymm _ _ huv hvw)
  · intro w a bs w' a' bs' l _ _ _ _ hne _
    rcases hs.total w w' with h | h
    · exact .inl ⟨h, hne⟩
    · exact .inr ⟨h, Ne.symm hne⟩
  · intro w w' h h'
    refine ⟨hrs w w' (.inr ⟨h, h'⟩), ?_⟩
    rintro rfl
    exact h' h

/-- Final-memory constraints are satisfiable for every execution: a coherence order exists; a
write that every other write to a byte precedes is that byte's only co-maximal write, and the
value the co-maximal writes of a byte agree on is unique. -/
theorem final_exists (X : Execution) : ∃ m, IsFinal L mem0 X m := by
  classical
  obtain ⟨co, hco⟩ := coOrder_exists (L := L) X
  let P : Loc → Option Byte → Prop := fun l v => (∃ w, CoMaximal X co l w) ∧
    ∀ w a bs, CoMaximal X co l w → X.MemWrites w a bs → wbyte a bs l = v
  have unique : ∀ l v v', P l v → P l v' → v = v' := by
    rintro l v v' ⟨⟨w, hmax⟩, hv⟩ ⟨-, hv'⟩
    obtain ⟨a, bs, hw, -⟩ := hmax.1
    exact (hv w a bs hmax hw).symm.trans (hv' w a bs hmax hw)
  let m : FinalMem := fun l => if h : ∃ v, P l v then some (Classical.choose h) else mem0 l
  have hm : ∀ l v, P l v → m l = some v := by
    intro l v hv
    have hex : ∃ v, P l v := ⟨v, hv⟩
    simp only [m, dite_eq_left hex]
    exact congrArg some (unique l _ _ (Classical.choose_spec hex) hv)
  refine ⟨m, co, hco, fun l => ⟨?_, ?_, fun v hex hv => hm l v ⟨hex, hv⟩⟩⟩
  · intro e a bs he hel hlast
    have hmax : CoMaximal X co l e := ⟨⟨a, bs, he, hel⟩, fun w a' bs' hw hc h => by
      rcases hlast w a' bs' hw hc with rfl | hwe
      · exact hco.irrefl _ h
      · exact hco.irrefl _ (hco.trans _ _ _ h hwe)⟩
    refine hm l _ ⟨⟨e, hmax⟩, fun w a' bs' hwm hw => ?_⟩
    obtain ⟨⟨a0, bs0, hw0, hc0⟩, hwmax⟩ := hwm
    rcases hlast w a0 bs0 hw0 hc0 with rfl | hwe
    · obtain ⟨⟨hla, -⟩, hbs⟩ := Execution.MemWrites.unique he hw
      simp only [wbyte, hbs, hla]
    · exact absurd hwe (hwmax e a bs he hel)
  · intro hn
    have hex : ¬ ∃ v, P l v := by
      rintro ⟨v, ⟨w, ⟨a, bs, hw, hc⟩, -⟩, -⟩
      exact hn w a bs hw hc
    simp only [m, dite_eq_right hex]

/-- In particular the theorem's quantified executions include a completed execution,
provided its optional assumptions admit the empty prefix. -/
theorem Correct.complete_exists {post : FinalMem → Prop} (hc : Correct K A L mem0 post)
    (hv : L.Valid K) (hA : ∀ a ∈ A, a.wf L mem0 Execution.empty) :
    ∃ X, Consistent L K A mem0 X ∧ Complete L X := by
  obtain ⟨X, hX, -, hdone⟩ := hc.complete_extension hv (consistent_empty hv.1 hA)
  exact ⟨X, hX, hdone⟩

/-- There actually exists an output memory satisfying the proved postcondition. -/
theorem Correct.output_exists {post : FinalMem → Prop} (hc : Correct K A L mem0 post)
    (hv : L.Valid K) (hA : ∀ a ∈ A, a.wf L mem0 Execution.empty) :
    ∃ X m, Consistent L K A mem0 X ∧ Complete L X ∧ IsFinal L mem0 X m ∧ post m := by
  obtain ⟨X, hX, hdone⟩ := hc.complete_exists hv hA
  obtain ⟨m, hm⟩ := final_exists (L := L) (mem0 := mem0) X
  exact ⟨X, m, hX, hdone, hm, hc.result hv X m hX hdone hm⟩

end
end
end PTX
