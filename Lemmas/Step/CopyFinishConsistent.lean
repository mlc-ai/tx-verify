-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Step.CopyFinishMemory
public import Lemmas.Step.CopyFinishWaiting

public import Lemmas.Step.SetMaxNReg
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc

@[expose] public section

namespace PTX
open AsyncCopy MBarrier
noncomputable section

/-- Every stage present before the completion is present after it. -/
theorem finishCopyRecord_present_of_old {X : Execution} {i : EvId} {bs : List Byte}
    {src : Nat → Option Ref} {mb : Loc} {rec : Record Ref} {x : Ref} (h : X.RefPresent x) :
    (X.finishCopyRecord i bs src mb rec).RefPresent x := by
  by_cases hx : CopyRef i x
  · obtain ⟨p, rfl, hp⟩ := hx
    rcases hp with rfl | rfl | rfl <;>
      simp [Execution.RefPresent, Execution.AsyncPresent, Execution.finishCopyRecord,
        Execution.appendObject, Execution.finishCopy]
  · exact (finishCopyRecord_present_old hx).mpr h

/-- The completion of a copy that writes its destination as one whole changes no atomic
read-modify-write, no old-value source and no moral strength of one (MEM-ATOMICITY). -/
theorem finishCopyRecord_atomicOk {L : Launch} {X : Execution} {i : EvId} {bs : List Byte}
    {src : Nat → Option Ref} {mb : Loc} {rec : Record Ref} (h : AtomicOk L X) :
    AtomicOk L (X.finishCopyRecord i bs src mb rec) := by
  have hcp : ∀ j k, ((X.finishCopyRecord i bs src mb rec).async.copies j).elemWrites k =
      (X.async.copies j).elemWrites k := by
    intro j k
    by_cases hj : j = i
    · subst j; simp [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy]
    · simp [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy, hj]
  have hrmw : ∀ p l n, (X.finishCopyRecord i bs src mb rec).RmwAt p l n ↔ X.RmwAt p l n := by
    intro p l n
    cases p with
    | thread e => rfl
    | tensor j x y => rfl
    | copy j k => simp only [Execution.RmwAt, hcp]; rfl
  have hold : ∀ p k, (X.finishCopyRecord i bs src mb rec).oldRf p k = X.oldRf p k := by
    intro p k
    cases p <;> simp [Execution.oldRf, Execution.finishCopyRecord, Execution.appendObject,
      Execution.finishCopy]
  have hstrong : ∀ p q, RmwStrong L (X.finishCopyRecord i bs src mb rec) p q ↔
      RmwStrong L X p q := fun _ _ => Iff.rfl
  have hreads : ∀ p q, AtomicReads L (X.finishCopyRecord i bs src mb rec) p q →
      AtomicReads L X p q := by
    rintro p q ⟨l, n, hp, hq, hs, k, k', hk, hr⟩
    exact ⟨l, n, (hrmw p l n).mp hp, (hrmw q l n).mp hq, (hstrong p q).mp hs, k, k', hk,
      by rwa [hold] at hr⟩
  refine ⟨fun p q l n k hp hq hne hs hk => ?_, fun p hc => ?_⟩
  · rw [hold, hold]
    exact h.unique p q l n k ((hrmw p l n).mp hp) ((hrmw q l n).mp hq) hne ((hstrong p q).mp hs) hk
  · exact h.acyclic p (Relation.TransGen.mono hreads _ _ hc)

/-- Complete one copy from a proved read-only source, retaining all prior observations.
The copy completes through an mbarrier and writes its destination as one whole. The caller
supplies the checked object transition, tcgen05 constraints and any explicit assumptions through
`htma` and `hasm`; none are inferred from successful completion. -/
theorem consistent_finishCopyRecord_initial {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {mb : Loc} {rec : Record Ref} {spec : Spec}
    (hX : Consistent L K A mem0 X) (hi : issuedBy X i = some spec)
    (hm : spec.completion = .mbarrier mb) (hw : spec.writes = .whole)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    (hsource : ∀ k < spec.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (spec.src.loc.at k))
    (hle : X.le (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec))
    (htma : TmaOk (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec))
    (hread : TcMma.ReadOk L A
      (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec))
    (hasm : ∀ a ∈ A, a.wf L mem0
      (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb rec)) :
    Consistent L K A mem0 (X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ =>
      none) mb rec) := by
  have hframe := finishCopyRecord_sinkFrame (bs := initialBytes mem0 X spec.src)
    (src := fun _ => none) (mb := mb) hX hi hm hw hn hid
  have horder := hframe.orderOk hX.orderOk
  exact {
    thr := hX.thr
    outside := hX.outside
    rf := finishCopyRecord_initial_rf hX hi hle
    ctaBar := hX.ctaBar
    cluster := hX.cluster
    dependency := {
      ready := fun e hr n hn' => by
        rw [finishCopyRecord_needs hX.tma.2.2.1 hn hid] at hn'
        have h := hX.dependency.ready e hr n hn'
        cases n with
        | node fills =>
          obtain ⟨x, hx, hf⟩ := h
          exact ⟨x, finishCopyRecord_present_of_old hx, hf⟩
        | cond holds => exact h
      acyclic := horder.depAcyclic }
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
    noFuture := finishCopyRecord_initial_noFuture hX hi hm hn hid hle
    hidden := finishCopyRecord_initial_hidden hX hi hm hn hid hsource hle
    tma := htma
    clc := hX.clc
    tensor := hX.tensor
    store := hX.store
    reduce := ⟨hX.reduce.values, fun j s r k v hc hr hs hv => by
      by_cases hj : j = i
      · subst j
        rw [Execution.Copy.unique (X := X) hc (issuedBy_some.mp hi), hw] at hr
        cases hr
      · have hcp : ((X.finishCopyRecord i (initialBytes mem0 X spec.src) (fun _ => none) mb
            rec).async.copies j) = X.async.copies j := by
          simp [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy, hj]
        rw [hcp] at hs hv ⊢
        exact hX.reduce.copies j s r k v hc hr hs hv⟩
    atomic := finishCopyRecord_atomicOk hX.atomic
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, fun e f hs hc =>
      hX.fenceSc.causal e f hs ((finishCopyRecord_baseCausality_iff hid).mp hc)⟩
    tmemPair := hX.tmemPair
    tmemPairCompletion := Tmem.Pair.completionClosed_of_trace_growth hle.1 rfl rfl hX.tmemPair
      hX.tmemPairCompletion
    tmemPairResult := hX.tmemPairResult
    tcCommit := hX.tcCommit
    mmaCompletion := TcMma.completionClosed_of_growth hle rfl hX.tma.2.1 hX.mmaCompletion
    tcRead := hread
    asm := hasm }

end
end PTX
