-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValueReload
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
import Kernels.TmlFa4Fwd.Flow.Code.Part019
import Kernels.TmlFa4Fwd.Flow.Code.Part020
import Lemmas.Flow.NotRmw
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue

noncomputable section

private def warmVSecondReload : SavedPointerReload := ⟨1292, 7292, 8, 2098, 2099⟩

private theorem warmValueColumnMask (tid : Nat) :
    (16 * tid &&& 112) = 16 * (tid % 8) := by
  have h := congrArg (fun n => n <<< 4) (Nat.and_two_pow_sub_one_eq_mod tid 3)
  change (tid &&& 7) <<< 4 = (tid % 8) <<< 4 at h
  rw [Nat.shiftLeft_and_distrib] at h
  simpa only [Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul, Nat.mul_comm _ 16] using h

private theorem warmValueMaskedColumn {l : Launch} {g tid : Nat} (hTid : tid < 512) :
    Seg kernel [] l g 2 1242 [(2066, b32 (16 * tid))] 1244 [(7721, b64 (16 * (tid % 8)))] := by
  have hFit : 16 * tid < 4294967296 := by omega
  have hFit64 : 16 * tid < 18446744073709551616 := by omega
  have hMasked : (16 * tid % 4294967296 &&& 112) = 16 * (tid % 8) := by
    rw [Nat.mod_eq_of_lt hFit, warmValueColumnMask]
  have hMasked64 : (16 * tid % 18446744073709551616 &&& 112) = 16 * (tid % 8) := by
    rw [Nat.mod_eq_of_lt hFit64, warmValueColumnMask]
  intro s hs
  seg_fp hs using
    norm_bits [Nat.mod_eq_of_lt hFit, Nat.mod_eq_of_lt hFit64,
      hMasked, hMasked64, warmValueColumnMask]

set_option maxRecDepth 100000 in
theorem warmMaskedColumnPrepared {l : Launch} {g tid : Nat} {s : TState}
    (hTid : tid < 512) {F : List (Nat × Value)} (hs : At s 1242 F)
    (hColumn : (2066, b32 (16 * tid)) ∈ F)
    (hFrame : ((kernel.code.drop 1242).take 2).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 1244 ((7721, b64 (16 * (tid % 8))) :: F) := by
  obtain ⟨u, hu, hU⟩ := warmValueMaskedColumn (g := g) hTid s
    (hs.mono ⟨holds_mem hs.2.2.2.2 hColumn, trivial⟩)
  obtain ⟨hRun, hKeep⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    hFrame rfl hu
  have hF := holdsSchedulerFrame hs.2.2.2.2 hKeep (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, run_rtg hRun, hU.mono ⟨hU.2.2.2.2.1, hF⟩⟩

set_option maxRecDepth 100000 in
/-- Replay the upper pointer load using the earlier lane-local save, and retain
the column shared by all later pairs. -/
theorem warmSecondValuePointerReloadFromCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {thread index batch head row trips warp tid j : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (hTid : tid < 512)
    {s : TState} {ending : Option TState}
    (hs : At s 1227 (warmCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop index) ending)
    (hSaved : ∃ write < index, X.Writes (thread, write) (pointerSaveAccess l thread 1 1)
        (b64 (primingVRowPointer p batch head row)).toBytes ∧
      ∀ k < 8, ∀ n < index, ∀ a, X.Access (thread, n) a true →
        a.Covers ((pointerSaveAccess l thread 1 1).loc.at k) → n ≤ write)
    {e : Event} (he : X.get (thread, j) = some e) (hBefore : index ≤ j)
    (hLate : 1292 < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    let ptr := primingVRowPointer p batch head row
    ∃ pos, pos + 2 ≤ j ∧
      ((X.tr thread).take (pos + 2)).countP Execution.isShfl =
        ((X.tr thread).take index).countP Execution.isShfl + 16 ∧
      ∃ u stop,
        At u 1293 ([(2098, b32 (ptr % 2 ^ 32)), (2099, b32 (ptr / 2 ^ 32)),
          (7721, b64 (16 * (tid % 8)))] ++ warmCacheFrame p l batch head trips warp tid) ∧
        Run kernel Assumptions.all l thread u ((X.tr thread).drop (pos + 2)) stop := by
  let ptr := primingVRowPointer p batch head row
  let baseFrame := warmCacheFrame p l batch head trips warp tid
  let columnFrame := (2066, b32 (16 * tid)) :: baseFrame
  let F := (7721, b64 (16 * (tid % 8))) :: columnFrame
  let site := warmVSecondReload
  obtain ⟨pre, hLocal, hPre⟩ := warmValueColumnPrepared (g := thread) hTid hs
  have preRun := hr.after_local_nonempty hLocal (traceAfterObservedEvent he hBefore)
  have firstAudit (bound : Nat) : ((kernel.code.drop 1228).take (1242 - 1228)).all
      (fun ins => loaderPipelineCutOp 1228 1242 bound (columnFrame.map Prod.fst) ins.op) =
        true := by
    kernel_rfl
  have firstRanked : (((kernel.code.drop 1228).take (1242 - 1228)).zipIdx 1228).all
      (fun (ins, pc) => LoaderRankedInstr 1242 pc ins) = true := by kernel_rfl
  obtain ⟨first, early, earlyStop, _, hFirst, firstRun, firstRank, firstBefore⟩ :=
    prefixRankedShuffleCut (by decide) firstAudit firstRanked hPre preRun he hBefore
      (.inl (by omega)) hSafe
  obtain ⟨column, hLocal, hColumn⟩ := warmMaskedColumnPrepared (g := thread) hTid
    hFirst (by simp [columnFrame]) (by kernel_rfl)
  have hLive := traceAfterObservedEvent he firstBefore
  have columnRun := firstRun.after_local_nonempty hLocal hLive
  have hAudit (bound : Nat) : ((kernel.code.drop 1244).take (1292 - 1244)).all
      (fun ins => loaderPipelineCutOp 1244 1292 bound (F.map Prod.fst) ins.op) = true := by
    kernel_rfl
  have hRanked : (((kernel.code.drop 1244).take (1292 - 1244)).zipIdx 1244).all
      (fun (i, pc) => LoaderRankedInstr 1292 pc i) = true := by kernel_rfl
  obtain ⟨u, later, stop, _, hu, huRun, huRank, huBefore⟩ :=
    prefixRankedShuffleCut (by decide) hAudit hRanked hColumn columnRun he firstBefore
      (.inl hLate.le) hSafe
  let nextIndex := index + early.length + later.length
  have firstCount : loaderShuffleTail 1242 1228 = 2 := by kernel_rfl
  have restCount : loaderShuffleTail 1292 1244 = 14 := by kernel_rfl
  have upperCount : loaderShuffleTail 1294 1227 = 17 := by kernel_rfl
  have upperAudit (n : Nat) : ((kernel.code.drop 1227).take (1294 - 1227)).all
      (fun ins => loaderPipelineCutOp 1227 1294 n [] ins.op) = true := by kernel_rfl
  have upperRanked : (((kernel.code.drop 1227).take (1294 - 1227)).zipIdx 1227).all
      (fun (ins, pc) => LoaderRankedInstr 1294 pc ins) = true := by kernel_rfl
  obtain ⟨write, hOrder, hSaved, hLast⟩ := hSaved
  have hLast' (byte : Nat) (hByte : byte < 8) (k : Nat) (hk : k < nextIndex) (a : Acc)
      (hA : X.Access (thread, k) a true)
      (hc : a.Covers ((site.cell thread l.localBase).loc.at byte)) :
      k ≤ write := by
    by_cases hOld : k < index
    · apply hLast byte hByte k hOld a hA
      exact hc
    have hj : j < (X.tr thread).length := (List.getElem?_eq_some_iff.mp he).1
    have hPresent : k < (X.tr thread).length := by change nextIndex ≤ j at huBefore; omega
    let ev := (X.tr thread)[k]
    have hGet : X.get (thread, k) = some ev := List.getElem?_eq_getElem hPresent
    have hMono := countP_take_mono Execution.isShfl (X.tr thread) hk.le
    have hBudget : ((X.tr thread).take k).countP Execution.isShfl <
        ((X.tr thread).take index).countP Execution.isShfl + loaderShuffleTail 1294 1227 := by
      change ((X.tr thread).take k).countP Execution.isShfl ≤
        ((X.tr thread).take nextIndex).countP Execution.isShfl at hMono
      rw [upperCount]
      change ((X.tr thread).take nextIndex).countP Execution.isShfl =
        ((X.tr thread).take (index + early.length)).countP Execution.isShfl +
          loaderShuffleTail 1292 1244 at huRank
      change ((X.tr thread).take (index + early.length)).countP Execution.isShfl =
        ((X.tr thread).take index).countP Execution.isShfl +
          loaderShuffleTail 1242 1228 at firstRank
      rw [huRank, firstRank, firstCount, restCount] at hMono
      omega
    have hBounds := loaderRankedEventBounds (by decide) upperAudit upperRanked
      hs hr hGet (by omega) hBudget
    exact (noOrdinaryWritesBeforeValueBroadcast hX hGet hBounds hA).elim
  have hFit : ptr < 2 ^ 64 := by
    have hPage := primingScratchPageBound hp (row := row) hb
    obtain ⟨hEq, hFit, _⟩ := sourceScratchPayload_live hp 1 hPage (Nat.mod_lt row (by decide)) hh
    have hEqual : _ = ptr := hEq
    rwa [hEqual] at hFit
  have hCode : kernel.code[site.pc]? = some ⟨none, .mem site.mem⟩ := Flow.code_1292
  have hAddr : l.localBase + site.offset < 2 ^ 64 := by
    have h := hp.localMemory.2.1
    change l.localBase + 8 < 2 ^ 64
    omega
  have hAlign : (l.localBase + site.offset) % 8 = 0 := by
    have h := hp.localMemory.1
    change (l.localBase + 8) % 8 = 0
    omega
  have hInput : At u site.pc ((site.baseReg, b64 l.localBase) :: F) :=
    hu.mono ⟨holds_lookup hu.2.2.2.2 rfl, hu.2.2.2.2⟩
  have hFresh : ∀ pair ∈ F, pair.1 ≠ site.lowReg ∧ pair.1 ≠ site.highReg := by
    intro pair hm
    have ha : (F.map Prod.fst).all (fun r => decide (r ≠ 2098 ∧ r ≠ 2099)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp ha _ (List.mem_map_of_mem hm))
  have hDemand : PrefixDemand X thread nextIndex 1292 stop := .inr ⟨j, e, huBefore, hLate, he⟩
  have hSave : X.Writes (thread, write) (site.cell thread l.localBase)
      (b64 ptr).toBytes := hSaved
  obtain ⟨v, hv, hvF, hvRun, hLow, hHigh⟩ :=
    site.observedInPrefix hX (index := nextIndex) (bound := 1292)
    (by decide)
    hCode hAddr hAlign (by decide) hFit (by unfold nextIndex; omega)
    hInput hFresh (by decide) huRun hDemand hSave hLast'
  have strictlyAfter {n : Nat} {read : Event} (hGet : X.get (thread, n) = some read)
      (hRead : read.pc = 1292) : n ≠ j := by
    intro hEq
    subst j
    have same := Option.some.inj (hGet.symm.trans he)
    rw [← same, hRead] at hLate
    omega
  have h1 := strictlyAfter hLow rfl
  have h2 := strictlyAfter hHigh rfl
  have hvRank := (countShuffleTakeOfNonshuffle hHigh rfl).trans
    ((countShuffleTakeOfNonshuffle hLow rfl).trans huRank)
  rw [firstRank, firstCount, restCount, Nat.add_assoc] at hvRank
  exact ⟨nextIndex, by omega, hvRank, v, stop,
    hv.mono ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.1, hvF.1, hvF.2.2⟩, hvRun⟩


end
end PTX.Kernels.TmlFa4Fwd.Loader
