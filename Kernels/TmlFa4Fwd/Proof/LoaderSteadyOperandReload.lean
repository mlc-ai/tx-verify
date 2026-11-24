-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyOperandSpills
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
import Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
import Kernels.TmlFa4Fwd.Proof.LoaderSteadyWideColumn
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Flow.Code.Part024
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part026
import Lemmas.Flow.NotRmw
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Epilogue

noncomputable section

/-- The ordinary vector load for the lower or upper steady pointer. -/
def steadyPointerReload (value : Bool) (slot : Fin 2) : SavedPointerReload :=
  let i := steadySpillSite value
  let regs := pointerSlotReloadRegs i slot
  ⟨pointerSlotReloadPc i slot, pointerReloadBase i, 8 * slot.val, regs.1, regs.2⟩

private theorem steadyPointerReloadCode (value : Bool) (slot : Fin 2) :
    kernel.code[(steadyPointerReload value slot).pc]? =
      some ⟨none, .mem (steadyPointerReload value slot).mem⟩ := by
  cases value <;> fin_cases slot
  · exact Flow.code_1469
  · exact Flow.code_1537
  · exact Flow.code_1632
  · exact Flow.code_1685

private theorem noWriteInDecodedSlice {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i first last : Nat} {e : Event} (he : X.get (g, i) = some e)
    (hPc : first ≤ e.pc ∧ e.pc < last)
    (hAudit : ((kernel.code.drop first).take (last - first)).all
      (fun ins => !writeOp ins.op && !atomicOp ins.op) = true)
    {a : Acc} (hA : X.Access (g, i) a true) : False := by
  have codeAt {ins : Instr} (hCode : kernel.code[e.pc]? = some ins) :
      (!writeOp ins.op && !atomicOp ins.op) = true := by
    apply List.all_eq_true.mp hAudit
    apply List.mem_of_getElem? (i := e.pc - first)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hPc.1]
    exact hCode
  rcases hA with ⟨_, _, hFalse⟩ | ⟨data, ⟨pc, hGet⟩, _⟩ | ⟨old, new, pc, hGet⟩
  · cases hFalse
  · obtain rfl := Option.some.inj (he.symm.trans hGet)
    rcases get_source hX he with ⟨_, h⟩ | ⟨_, ins, _, _, hc, hf⟩
    · cases h
    have h := codeAt hc
    rw [fires_write_op hf rfl] at h
    cases h
  · obtain rfl := Option.some.inj (he.symm.trans hGet)
    rcases get_source hX he with ⟨_, h⟩ | ⟨_, ins, _, _, hc, hf⟩
    · cases h
    have h := Bool.and_eq_true_iff.mp (codeAt hc)
    rw [fires_rmw_op hf rfl] at h
    cases h.2

/-- The first V address calculation also seeds the upper-half lane column. -/
def steadyReloadColumn (wide : Bool) (tid : Nat) : List (Nat × Value) :=
  if wide then [(7825, b64 (16 * (tid % 8)))] else []

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index j batch head row trips warp tid : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (value : Bool)
include hp hX hb hh value

set_option maxRecDepth 100000 in
/-- The steady copy broadcasts consume the two words of their actual saved pointer. -/
theorem steadyOperandReloadFromSpillsWithColumn (slot : Fin 2) (wide : Bool)
    (hWide : wide = true → value = true ∧ slot = 1) {s : TState} {ending : Option TState}
    (hs : At s (steadySpillExit value) (steadyCacheFrame p l batch head trips warp tid))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hSaved : ∃ write < index,
      X.Writes (g, write) (pointerSaveAccess l g (steadySpillSite value) slot)
        (b64 (steadyOperandPointer p value batch head row)).toBytes ∧
      ∀ byte < 8, ∀ k < index, ∀ a, X.Access (g, k) a true →
        a.Covers ((pointerSaveAccess l g (steadySpillSite value) slot).loc.at byte) → k ≤ write)
    {e : Event} (he : X.get (g, j) = some e) (hBefore : index ≤ j)
    (hLate : (steadyPointerReload value slot).pc < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    let load := steadyPointerReload value slot
    let ptr := steadyOperandPointer p value batch head row
    ∃ pos, pos + 2 ≤ j ∧ ∃ u stop,
      At u (load.pc + 1) ([(load.lowReg, b32 (ptr % 2 ^ 32)),
        (load.highReg, b32 (ptr / 2 ^ 32))] ++
          (steadyReloadColumn wide tid ++ steadyCacheFrame p l batch head trips warp tid)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 2)) stop ∧
      ((X.tr g).take (pos + 2)).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 16 * slot.val := by
  let load := steadyPointerReload value slot
  let ptr := steadyOperandPointer p value batch head row
  let F := steadyCacheFrame p l batch head trips warp tid
  let G := steadyReloadColumn wide tid ++ F
  let low := steadySpillExit value
  let hi := load.pc + 2
  let addr := pointerReloadAddress l (steadySpillSite value)
  have hCheckpoint : ∃ pos, index ≤ pos ∧ pos ≤ j ∧ ∃ t stop,
      At t load.pc G ∧ Run kernel Assumptions.all l g t ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 16 * slot.val := by
    by_cases hColumn : wide = true
    · obtain ⟨rfl, rfl⟩ := hWide hColumn
      subst wide
      have hLate' : 1685 < e.pc := hLate
      have hFrom : At s 1632 F := hs
      obtain ⟨index', hBeforeWide, hWideBefore, u, mid, hu, huRun, huRank⟩ :=
        steadyValueWideColumnOfEvent (tid := tid) (by decide)
          (fun _ => by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
          (by simp [F, steadyCacheFrame]) hFrom hr he hBefore (.inl (by omega)) hSafe
      have huAt : At u 1637 G := hu
      obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
        prefixRankedShuffleCut (start := 1637) (stop := 1685) (by decide)
          (fun _ => by kernel_rfl) (by kernel_rfl) huAt huRun he hWideBefore
          (.inl hLate'.le) hSafe
      have hFirst : loaderShuffleTail 1636 1632 = 2 := by kernel_rfl
      have hSecond : loaderShuffleTail 1685 1637 = 14 := by kernel_rfl
      refine ⟨index' + front.length, by omega, htBefore, t, stop, ht, htRun, ?_⟩
      rw [htRank, huRank, hFirst, hSecond]
      change _ + 2 + 14 = _ + 16
      omega
    · have hFalse : wide = false := Bool.eq_false_of_not_eq_true hColumn
      subst wide
      have hSpan : 174 ≤ low ∧ low ≤ load.pc ∧ load.pc ≤ 1901 := by
        cases value <;> fin_cases slot <;> decide
      have hAudit (n : Nat) : ((kernel.code.drop low).take (load.pc - low)).all
          (fun ins => loaderPipelineCutOp low load.pc n (F.map Prod.fst) ins.op) = true := by
        cases value <;> fin_cases slot <;> kernel_rfl
      have hRanked : (((kernel.code.drop low).take (load.pc - low)).zipIdx low).all
          (fun (ins, pc) => LoaderRankedInstr load.pc pc ins) = true := by
        cases value <;> fin_cases slot <;> kernel_rfl
      obtain ⟨t, front, stop, _, ht, htRun, htCount, htBefore⟩ :=
        prefixRankedShuffleCut hSpan hAudit hRanked hs hr he hBefore (.inl hLate.le) hSafe
      let pos := index + front.length
      have hCount : loaderShuffleTail load.pc low = 16 * slot.val := by
        cases value <;> fin_cases slot <;> kernel_rfl
      have hAtCount : ((X.tr g).take pos).countP Execution.isShfl =
          ((X.tr g).take index).countP Execution.isShfl + 16 * slot.val := by
        simpa only [hCount] using htCount
      exact ⟨pos, Nat.le_add_right _ _, htBefore, t, stop, ht, htRun, hAtCount⟩
  obtain ⟨pos, hFrom, htBefore, t, stop, ht, htRun, hAtCount⟩ := hCheckpoint
  have hCountHi : loaderShuffleTail hi low = 16 * slot.val + 1 := by
    cases value <;> fin_cases slot <;> kernel_rfl
  have hSpanHi : 174 ≤ low ∧ low ≤ hi ∧ hi ≤ 1901 := by
    cases value <;> fin_cases slot <;> decide
  have hAuditHi (n : Nat) : ((kernel.code.drop low).take (hi - low)).all
      (fun ins => loaderPipelineCutOp low hi n [] ins.op) = true := by
    cases value <;> fin_cases slot <;> kernel_rfl
  have hRankedHi : (((kernel.code.drop low).take (hi - low)).zipIdx low).all
      (fun (ins, pc) => LoaderRankedInstr hi pc ins) = true := by
    cases value <;> fin_cases slot <;> kernel_rfl
  have hQuiet : ((kernel.code.drop low).take (hi - low)).all
      (fun ins => !writeOp ins.op && !atomicOp ins.op) = true := by
    cases value <;> fin_cases slot <;> kernel_rfl
  have hCell : load.cell g addr = pointerSaveAccess l g (steadySpillSite value) slot := by
    cases value <;> fin_cases slot <;> rfl
  obtain ⟨write, hWriteBefore, hWrite, hLatest⟩ := hSaved
  have hLast (byte : Nat) (hByte : byte < 8) (k : Nat) (hk : k < pos) (a : Acc)
      (hAccess : X.Access (g, k) a true) (hCover : a.Covers ((load.cell g addr).loc.at byte)) :
      k ≤ write := by
    by_cases hPast : k < index
    · rw [hCell] at hCover
      exact hLatest byte hByte k hPast a hAccess hCover
    have hPresent : k < (X.tr g).length := by
      have heLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
      omega
    let here := (X.tr g)[k]
    have hGet : X.get (g, k) = some here := List.getElem?_eq_getElem hPresent
    have hBound : ((X.tr g).take k).countP Execution.isShfl <
        ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail hi low := by
      rw [hCountHi, ← Nat.add_assoc, ← hAtCount]
      exact Nat.lt_succ_of_le (countP_take_mono Execution.isShfl _ hk.le)
    have hP := loaderRankedEventBounds hSpanHi hAuditHi hRankedHi hs hr hGet
      (Nat.le_of_not_gt hPast) hBound
    exact (noWriteInDecodedSlice hX hGet hP hQuiet hAccess).elim
  let cache := recurringCache p (steadySpillSite value)
  have hPage : primingScratchPage p batch row < p.pages := primingScratchPageBound hp hb
  have hRow : row % 16 < 16 := Nat.mod_lt _ (by decide)
  have hCache : cache.region p.pages p.kvHeads ∈ p.inputRegions := by
    cases value <;> simp [cache, recurringCache, steadySpillSite, Params.inputRegions]
  have hFit : ptr < 2 ^ 64 := by
    have hLoc := CacheLayout.loc_copy_in_region (c := cache) hPage hh hRow
      (d := 0) (byte := 0) (by decide)
    have hRange := hp.ranges (cache.region p.pages p.kvHeads) (by simp [hCache])
    exact hLoc.2.2.2.trans_le hRange
  let extra := if value then 8 * slot.val else 32 + 8 * slot.val
  have hOffsets : addr + load.offset = l.localBase + extra := by
    cases value <;> fin_cases slot <;> dsimp [addr, load, extra, pointerReloadAddress,
      steadyPointerReload, steadySpillSite]
  have hAddress : addr + load.offset < 2 ^ 64 := by
    rw [hOffsets]
    have hm := hp.localMemory.2.1
    have hSize : extra ≤ 40 := by cases value <;> fin_cases slot <;> decide
    omega
  have hAlign : (addr + load.offset) % 8 = 0 := by
    have hAligned : extra % 8 = 0 := by cases value <;> fin_cases slot <;> decide
    have hBase : l.localBase % 8 = 0 := by have h := hp.localMemory.1; omega
    rw [hOffsets, Nat.add_mod, hBase, hAligned]
  have hInput : At t load.pc ((load.baseReg, b64 addr) :: G) := by
    apply ht.mono
    have hF : Holds t.regs F := ((holds_append ..).mp ht.2.2.2.2).2
    exact ⟨by cases value <;> exact holds_lookup hF rfl, ht.2.2.2.2⟩
  have hFresh : ∀ q ∈ G, q.1 ≠ load.lowReg ∧ q.1 ≠ load.highReg := by
    intro q hQ
    have hAudit : (G.map Prod.fst).all (fun k => decide (k ≠ load.lowReg ∧ k ≠ load.highReg)) =
        true := by cases wide <;> cases value <;> fin_cases slot <;> rfl
    exact of_decide_eq_true (List.all_eq_true.mp hAudit _ (List.mem_map_of_mem hQ))
  have hNeed : PrefixDemand X g pos load.pc stop := .inr ⟨j, e, htBefore, hLate, he⟩
  obtain ⟨u, hu, huFrame, huRun, hLow, hHigh⟩ :=
    load.observedInPrefix hX (index := pos) (bound := load.pc)
      (by cases value <;> fin_cases slot <;> decide) (steadyPointerReloadCode value slot)
      hAddress hAlign (by cases value <;> fin_cases slot <;> decide)
      hFit (hWriteBefore.trans_le hFrom) hInput hFresh le_rfl htRun hNeed
      (by rwa [hCell]) hLast
  have afterRead {k : Nat} {read : Event} (hRead : X.get (g, k) = some read)
      (hReadPc : read.pc = load.pc) : k ≠ j := by
    intro hEq
    subst j
    have hSame := Option.some.inj (hRead.symm.trans he)
    exact Nat.lt_irrefl _ (by rwa [← hSame, hReadPc] at hLate)
  have hFirst := afterRead hLow rfl
  have hSecond := afterRead hHigh rfl
  refine ⟨pos, by omega, u, stop,
    hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.1, huFrame⟩, huRun, ?_⟩
  exact (countShuffleTakeOfNonshuffle hHigh rfl).trans
    ((countShuffleTakeOfNonshuffle hLow rfl).trans hAtCount)

end
end PTX.Kernels.TmlFa4Fwd.Loader
