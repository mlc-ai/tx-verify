-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValuePointerSave
import Kernels.TmlFa4Fwd.Flow.Code.Part019

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

private theorem warmValueSaveRoute {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)} (more : Bool)
    (hKeep : ((kernel.code.drop 1224).take 3).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 1224 ((10, .pred more) :: F)) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      At u (if more then 1211 else 1227) ((9538, b64 1) :: (777, .pred false) :: F) := by
  have core : Seg kernel [] l g 3 1224 [(10, .pred more)] (if more then 1211 else 1227)
      [(9538, b64 1), (777, .pred false)] := by
    cases more <;> intro t ht <;> seg_fp ht using rfl
  obtain ⟨u, hu, hU⟩ := core s (hs.mono ⟨hs.2.2.2.2.1, trivial⟩)
  obtain ⟨hRun, hFrame⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) hs.1 hKeep (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hF := holdsSchedulerFrame hs.2.2.2.2.2 hFrame (fun _ h => List.mem_map_of_mem h)
  exact ⟨u, hRun, hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1, hF⟩⟩

private theorem warmValueNextEntry {l : Launch} {g : Nat} {s : TState}
    {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop 1211).take 1).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 1211 ((9538, b64 1) :: (777, .pred false) :: F)) :
    ∃ u, run kernel Assumptions.all l g 1 s = some u ∧
      At u 1212 ((9538, b64 1) :: (10, .pred false) :: F) := by
  let u := next (setReg s 10 (.pred false))
  have hRun : run kernel [] l g 1 s = some u := by
    refine run_local Flow.code_1211 rfl hs ?_
    rw [execLocalA_nil]
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, readPred, readReg,
      hs.2.2.2.2.2.1, u, bind, Except.bind, pure, Except.pure]
  have hRegs : ((kernel.code.drop 1211).take 1).all
      (fun ins => (9538 :: F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
        true := by
    apply List.all_eq_true.mpr
    intro ins hm
    have hSrc : ((kernel.code.drop 1211).take 1).all
        (fun i => !(writesRegs i.op).contains 9538) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨List.all_eq_true.mp hSrc ins hm, List.all_eq_true.mp hKeep ins hm⟩
  obtain ⟨hr, hf⟩ := loaderLinear (regs := 9538 :: F.map Prod.fst)
    (by decide) (by decide) hs.1 hRegs rfl hRun
  have hU : At u 1212 [(10, .pred false)] := (hs.mono (G := []) trivial).set (by simp)
  exact ⟨u, hr, hU.mono ⟨(hf 9538 (by simp)).trans hs.2.2.2.2.1, hU.2.2.2.2.1,
    holdsSchedulerFrame hs.2.2.2.2.2.2 hf
      (fun r hm => .tail 9538 (List.mem_map_of_mem hm))⟩⟩

private theorem valuePointerCellsApart (l : Launch) (g byte : Nat) (hb : byte < 8) :
    ¬ (pointerSaveAccess l g 1 1).Covers ((pointerSaveAccess l g 1 0).loc.at byte) := by
  simp [pointerSaveAccess, pointerSaveAddress, pointerReloadAddress,
    Acc.Covers, Loc.InRange, Loc.at]
  omega

set_option maxRecDepth 100000 in
/-- Reuse authenticated page words to observe both V pointer saves and their
latest-byte witnesses at the local packet prelude. -/
theorem warmValuePointersFromPageHistory {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {thread j pagePos pos batch head trips warp tid tile : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads)
    (hPage0 : WarmPageWords p l X thread pagePos batch (primingLaneRow tile tid) 0)
    (hPage1 : WarmPageWords p l X thread
      (pagePos + primingScratchReads p batch (primingLaneRow tile tid) + 2)
      batch (primingLaneRow tile tid + 64) 1)
    {seed s : TState} {seedEnd ending : Option TState}
    (hSeed : At seed 957 (warmCacheFrame p l batch head trips warp tid))
    (hSeedRun : Run kernel Assumptions.all l thread seed ((X.tr thread).drop
      (pagePos + primingScratchReads p batch (primingLaneRow tile tid) + 2 +
        primingScratchReads p batch (primingLaneRow tile tid + 64) + 2)) seedEnd)
    (hBaseBefore : pagePos + primingScratchReads p batch (primingLaneRow tile tid) + 2 +
        primingScratchReads p batch (primingLaneRow tile tid + 64) + 2 ≤ pos)
    (hs : At s 1212 ([(9538, b64 0), (10, .pred true)] ++
      warmCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending)
    (hRankDelta : ((X.tr thread).take pos).countP Execution.isShfl =
      ((X.tr thread).take (pagePos + primingScratchReads p batch (primingLaneRow tile tid) + 2 +
        primingScratchReads p batch (primingLaneRow tile tid + 64) + 2)).countP
          Execution.isShfl + 32)
    {e : Event} (he : X.get (thread, j) = some e) (hBefore : pos ≤ j) (hPc : 1223 < e.pc) :
    ∃ final ≤ j, ∃ u,
      At u 1227 (warmCacheFrame p l batch head trips warp tid) ∧
      Run kernel Assumptions.all l thread u ((X.tr thread).drop final) ending ∧
      ((X.tr thread).take final).countP Execution.isShfl =
        ((X.tr thread).take pos).countP Execution.isShfl ∧
      ∀ slot : Fin 2, ∃ write < final,
        X.Writes (thread, write) (pointerSaveAccess l thread 1 slot)
          (b64 (primingVRowPointer p batch head
            (primingLaneRow tile tid + 64 * slot.val))).toBytes ∧
        ∀ k < 8, ∀ i < final, ∀ a, X.Access (thread, i) a true →
          a.Covers ((pointerSaveAccess l thread 1 slot).loc.at k) → i ≤ write := by
  let row := primingLaneRow tile tid
  have pageBefore0 : pagePos + primingScratchReads p batch row + 2 ≤ pos := by
    change pagePos + primingScratchReads p batch row + 2 +
      primingScratchReads p batch (row + 64) + 2 ≤ pos at hBaseBefore
    omega
  have latest0 := warmValuePageWordsLatest hp hX hPage0 hPage1 (hSeed.mono trivial) hSeedRun
    (stop := pos) (by rw [hRankDelta]) 0
  have hd : PrefixDemand X thread pos 1223 ending := .inr ⟨j, e, hBefore, hPc, he⟩
  obtain ⟨hPageRead0, hRowRead0, hSave0, a, ha, haRun⟩ :=
    warmValuePointerSave hp hX hb hh 0 true hPage0 pageBefore0 hs hr hd
      (fun target => by simpa using latest0 target)
  let second := pos + 3
  have hAfter : second ≤ j := afterObservedPointerSave he hBefore
    hPageRead0 hRowRead0 hSave0 hPc
    (show 1214 ≤ 1223 by decide) (show 1216 ≤ 1223 by decide) (show 1223 ≤ 1223 by decide)
  have hNextRank : ((X.tr thread).take second).countP Execution.isShfl =
      ((X.tr thread).take pos).countP Execution.isShfl := by
    have h0 := countShuffleTakeOfNonshuffle hPageRead0 rfl
    have h1 := countShuffleTakeOfNonshuffle hRowRead0 rfl
    have h2 := countShuffleTakeOfNonshuffle hSave0 rfl
    change ((X.tr thread).take (pos + 2 + 1)).countP Execution.isShfl = _
    rw [h2, show pos + 2 = pos + 1 + 1 by omega, h1, h0]
  obtain ⟨b, hbRun, hbAt⟩ := warmValueSaveRoute (l := l) (g := thread) true
    (by kernel_rfl) ha
  obtain ⟨c, hcRun, hcAt⟩ := warmValueNextEntry (l := l) (g := thread)
    (by kernel_rfl) hbAt
  have hc := haRun.after_local_nonempty (run_rtg (run_comp hbRun hcRun))
    (traceAfterObservedEvent he hAfter)
  have latest1 := warmValuePageWordsLatest hp hX hPage0 hPage1 (hSeed.mono trivial) hSeedRun
    (stop := second) (by rw [hNextRank, hRankDelta]) 1
  have pageBefore1 : pagePos + primingScratchReads p batch row + 2 +
      primingScratchReads p batch (row + 64) + 2 ≤ second := by
    change pagePos + primingScratchReads p batch row + 2 +
      primingScratchReads p batch (row + 64) + 2 ≤ pos at hBaseBefore
    unfold second
    omega
  have hd' : PrefixDemand X thread second 1223 ending := .inr ⟨j, e, hAfter, hPc, he⟩
  obtain ⟨hPageRead1, hRowRead1, hSave1, d, hdAt, hdRun⟩ :=
    warmValuePointerSave hp hX hb hh 1 false hPage1 pageBefore1 hcAt hc hd'
      (fun target => by simpa using latest1 target)
  let final := second + 3
  have hFinal : final ≤ j := afterObservedPointerSave he hAfter
    hPageRead1 hRowRead1 hSave1 hPc
    (show 1214 ≤ 1223 by decide) (show 1216 ≤ 1223 by decide) (show 1223 ≤ 1223 by decide)
  obtain ⟨u, hu, hU⟩ := warmValueSaveRoute (l := l) (g := thread) false
    (by kernel_rfl) hdAt
  have huRun := hdRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he hFinal)
  refine ⟨final, hFinal, u, hU.mono hU.2.2.2.2.2.2, huRun, ?_, ?_⟩
  · have h0 := countShuffleTakeOfNonshuffle hPageRead1 rfl
    have h1 := countShuffleTakeOfNonshuffle hRowRead1 rfl
    have h2 := countShuffleTakeOfNonshuffle hSave1 rfl
    change ((X.tr thread).take (second + 2 + 1)).countP Execution.isShfl = _
    rw [h2, show second + 2 = second + 1 + 1 by omega, h1, h0, hNextRank]
  intro slot
  fin_cases slot
  · refine ⟨pos + 2, by unfold final second; omega, ⟨1223, ?_⟩, ?_⟩
    · simpa [pointerSaveAccess, pointerSaveAddress, pointerReloadAddress] using hSave0
    intro k hk i hi a hAccess hCover
    by_contra! hBad
    have isOne : i = second ∨ i = second + 1 ∨ i = second + 2 := by
      unfold final at hi
      unfold second
      omega
    rcases isOne with rfl | rfl | rfl
    · exact observedReadNoWrite hPageRead1 hAccess
    · exact observedReadNoWrite hRowRead1 hAccess
    have hDst : a = pointerSaveAccess l thread 1 1 := by
      rcases hAccess with ⟨_, _, hFalse⟩ | ⟨bytes, ⟨pc, hOther⟩, _⟩ | ⟨old, new, pc, hOther⟩
      · cases hFalse
      · exact congrArg (fun k => match k with | .wr ac _ => ac | _ => a)
          (congrArg Event.kind (Option.some.inj (hOther.symm.trans hSave1)))
      · cases congrArg Event.kind (Option.some.inj (hOther.symm.trans hSave1))
    exact valuePointerCellsApart l thread k hk (hDst ▸ hCover)
  · refine ⟨second + 2, by unfold final; omega, ⟨1223, ?_⟩, ?_⟩
    · simpa [pointerSaveAccess, pointerSaveAddress, pointerReloadAddress] using hSave1
    · intro k hk i hi a hAccess hCover
      unfold final at hi
      omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
