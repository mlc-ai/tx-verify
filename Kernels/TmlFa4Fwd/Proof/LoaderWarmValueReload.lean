-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValueSaves
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
import Kernels.TmlFa4Fwd.Flow.Code.Part019
import Lemmas.Flow.NotRmw
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue

noncomputable section

private def warmVFirstReload : SavedPointerReload := ⟨1238, 7292, 0, 2077, 2078⟩

private theorem warmValueColumnCore {l : Launch} {g tid : Nat} (hTid : tid < 512) :
    Seg kernel [] l g 1 1227 [(1061, b32 tid)] 1228 [(2066, b32 (16 * tid))] := by
  have hFit : tid < 2 ^ 32 := by omega
  intro s hs
  seg_fp hs using
    norm_bits [Nat.mod_eq_of_lt hFit, Nat.shiftLeft_eq, Nat.mul_comm]

/-- The lane column instruction preserves the warm V pointer-save frame. -/
theorem warmValueColumnPrepared {p : Params} {l : Launch}
    {g batch head trips warp tid : Nat} {s : TState} (hTid : tid < 512)
    (hs : At s 1227 (warmCacheFrame p l batch head trips warp tid)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 1228 ((2066, b32 (16 * tid)) :: warmCacheFrame p l batch head trips warp tid) := by
  let F := warmCacheFrame p l batch head trips warp tid
  obtain ⟨u, hu, hU⟩ := warmValueColumnCore (g := g) hTid s
    (hs.mono ⟨holds_lookup hs.2.2.2.2 rfl, trivial⟩)
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    (by kernel_rfl) rfl hu
  have hFrame := holdsSchedulerFrame hs.2.2.2.2 huFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, run_rtg huA, hU.mono ⟨hU.2.2.2.2.1, hFrame⟩⟩

set_option maxRecDepth 100000 in
/-- Between the V saves and the first upper shuffle, no ordinary write reaches scratch. -/
theorem noOrdinaryWritesBeforeValueBroadcast {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i : Nat} {e : Event}
    (he : X.get (g, i) = some e) (hPc : 1227 ≤ e.pc ∧ e.pc < 1294)
    {a : Acc} (hA : X.Access (g, i) a true) : False := by
  have hf : ((kernel.code.drop 1227).take (1294 - 1227)).all
      (fun i => !writeOp i.op && !atomicOp i.op) = true := by kernel_rfl
  have inspect {ins : Instr} (h : kernel.code[e.pc]? = some ins) :
      (!writeOp ins.op && !atomicOp ins.op) = true := by
    apply List.all_eq_true.mp hf
    apply List.mem_of_getElem? (i := e.pc - 1227)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hPc.1]
    exact h
  rcases hA with ⟨_, _, hFalse⟩ | ⟨data, ⟨pc, hGet⟩, _⟩ | ⟨old, new, pc, hGet⟩
  · cases hFalse
  · obtain rfl := Option.some.inj (he.symm.trans hGet)
    rcases get_source hX he with ⟨_, h⟩ | ⟨_, ins, _, _, hc, hfire⟩
    · cases h
    have h := inspect hc
    rw [fires_write_op hfire rfl] at h
    cases h
  · obtain rfl := Option.some.inj (he.symm.trans hGet)
    rcases get_source hX he with ⟨_, h⟩ | ⟨_, ins, _, _, hc, hfire⟩
    · cases h
    have h := Bool.and_eq_true_iff.mp (inspect hc)
    rw [fires_rmw_op hfire rfl] at h
    cases h.2

set_option maxRecDepth 100000 in
/-- Recover the lower V pointer from the saved cell and preserve the lane column. -/
theorem warmFirstValueReloadFromSaves {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {thread i j batch head row trips warp tid : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (hTid : tid < 512)
    {s : TState} {ending : Option TState}
    (hs : At s 1227 (warmCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l thread s ((X.tr thread).drop i) ending)
    (hSaves : ∃ write < i, X.Writes (thread, write) (pointerSaveAccess l thread 1 0)
        (b64 (primingVRowPointer p batch head row)).toBytes ∧
      ∀ k < 8, ∀ n < i, ∀ a, X.Access (thread, n) a true →
        a.Covers ((pointerSaveAccess l thread 1 0).loc.at k) → n ≤ write)
    {e : Event} (he : X.get (thread, j) = some e) (hiBefore : i ≤ j)
    (hPc : 1238 < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    let ptr := primingVRowPointer p batch head row
    ∃ pos, pos + 2 ≤ j ∧ ∃ u stop,
      At u 1239 ([(2077, b32 (ptr % 2 ^ 32)), (2078, b32 (ptr / 2 ^ 32)),
        (2066, b32 (16 * tid))] ++ warmCacheFrame p l batch head trips warp tid) ∧
      Run kernel Assumptions.all l thread u ((X.tr thread).drop (pos + 2)) stop ∧
      ((X.tr thread).take (pos + 2)).countP Execution.isShfl =
        ((X.tr thread).take i).countP Execution.isShfl := by
  let ptr := primingVRowPointer p batch head row
  let F := warmCacheFrame p l batch head trips warp tid
  let G := (2066, b32 (16 * tid)) :: F
  obtain ⟨u, hLocal, huAt⟩ := warmValueColumnPrepared (g := thread) hTid hs
  have huRun := hr.after_local_nonempty hLocal (traceAfterObservedEvent he hiBefore)
  have hAudit (n : Nat) : ((kernel.code.drop 1228).take (1238 - 1228)).all
      (fun ins => loaderPipelineCutOp 1228 1238 n (G.map Prod.fst) ins.op) = true := by
    kernel_rfl
  have hRanked : (((kernel.code.drop 1228).take (1238 - 1228)).zipIdx 1228).all
      (fun (ins, pc) => LoaderRankedInstr 1238 pc ins) = true := by kernel_rfl
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut (by decide) hAudit hRanked huAt huRun he hiBefore
      (.inl hPc.le) hSafe
  let pos := i + front.length
  have hCount : loaderShuffleTail 1238 1228 = 0 := by kernel_rfl
  have hAtRank : ((X.tr thread).take pos).countP Execution.isShfl =
      ((X.tr thread).take i).countP Execution.isShfl := by
    simpa only [hCount, Nat.add_zero] using htRank
  have hInterval (n : Nat) : ((kernel.code.drop 1227).take (1240 - 1227)).all
      (fun ins => loaderPipelineCutOp 1227 1240 n [] ins.op) = true := by kernel_rfl
  have hIntervalRanked : (((kernel.code.drop 1227).take (1240 - 1227)).zipIdx 1227).all
      (fun (ins, pc) => LoaderRankedInstr 1240 pc ins) = true := by kernel_rfl
  have hIntervalCount : loaderShuffleTail 1240 1227 = 1 := by kernel_rfl
  obtain ⟨write, hOrder, hWrite, hLatest⟩ := hSaves
  let site := warmVFirstReload
  have hLast (k : Nat) (hk : k < 8) (j' : Nat) (hj : j' < pos) (a : Acc)
      (hA : X.Access (thread, j') a true)
      (hCover : a.Covers ((site.cell thread l.localBase).loc.at k)) :
      j' ≤ write := by
    by_cases hEarlier : j' < i
    · exact hLatest k hk j' hEarlier a hA hCover
    have hPresent : j' < (X.tr thread).length := by
      have hj : j < (X.tr thread).length := (List.getElem?_eq_some_iff.mp he).1
      change pos ≤ j at htBefore
      omega
    let ev := (X.tr thread)[j']
    have he' : X.get (thread, j') = some ev := List.getElem?_eq_getElem hPresent
    have hMark : ((X.tr thread).take j').countP Execution.isShfl <
        ((X.tr thread).take i).countP Execution.isShfl + loaderShuffleTail 1240 1227 := by
      rw [hIntervalCount, ← hAtRank]
      exact Nat.lt_succ_of_le (countP_take_mono Execution.isShfl (X.tr thread) hj.le)
    have hBounds := loaderRankedEventBounds (by decide) hInterval hIntervalRanked
      hs hr he' (Nat.le_of_not_gt hEarlier) hMark
    have hBeforeBroadcast : ev.pc < 1294 := hBounds.2.trans (by decide)
    exact (noOrdinaryWritesBeforeValueBroadcast hX he' ⟨hBounds.1, hBeforeBroadcast⟩ hA).elim
  have hPage := primingScratchPageBound hp (row := row) hb
  obtain ⟨hPtr, hFit, _⟩ := sourceScratchPayload_live hp 1 hPage (Nat.mod_lt row (by decide)) hh
  rw [hPtr] at hFit
  have hAt : At t site.pc ((site.baseReg, b64 l.localBase) :: G) :=
    ht.mono ⟨holds_lookup ht.2.2.2.2 rfl, ht.2.2.2.2⟩
  have hFresh : ∀ r ∈ G, r.1 ≠ site.lowReg ∧ r.1 ≠ site.highReg := by
    intro r hm
    have ha : (G.map Prod.fst).all (fun i => decide (i ≠ 2077 ∧ i ≠ 2078)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp ha _ (List.mem_map_of_mem hm))
  have hd : PrefixDemand X thread pos 1238 stop := .inr ⟨j, e, htBefore, hPc, he⟩
  have hStore : X.Writes (thread, write) (site.cell thread l.localBase) (b64 ptr).toBytes := by
    simpa [site, warmVFirstReload, SavedPointerReload.cell, pointerSaveAccess,
      pointerSaveAddress, pointerReloadAddress, ptr] using hWrite
  obtain ⟨v, hv, hvG, hvRun, hLow, hHigh⟩ := site.observedInPrefix hX
    (index := pos) (bound := 1238) (by decide) Flow.code_1238
    (by have h := hp.localMemory.2.1; change l.localBase + 0 < 2 ^ 64; omega)
    (by have h := hp.localMemory.1; change (l.localBase + 0) % 8 = 0; omega)
    (by decide) (show ptr < 2 ^ 64 from hFit) (by unfold pos; omega)
    hAt hFresh (by decide) htRun hd hStore hLast
  have notTarget {k : Nat} {read : Event} (hRead : X.get (thread, k) = some read)
      (hReadPc : read.pc = 1238) : k ≠ j := by
    intro hEq
    subst j
    have same := Option.some.inj (hRead.symm.trans he)
    rw [← same, hReadPc] at hPc
    omega
  have low := notTarget hLow rfl
  have high := notTarget hHigh rfl
  refine ⟨pos, by change pos ≤ j at htBefore; omega, v, stop,
    hv.mono ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.1, hvG⟩, hvRun, ?_⟩
  exact (countShuffleTakeOfNonshuffle hHigh rfl).trans
    ((countShuffleTakeOfNonshuffle hLow rfl).trans hAtRank)

end
end PTX.Kernels.TmlFa4Fwd.Loader
