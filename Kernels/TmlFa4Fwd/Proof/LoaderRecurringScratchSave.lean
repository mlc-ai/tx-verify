-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

private def scratchOffsetReg : Fin 4 → Nat
  | 0 => 7654
  | 1 => 7708
  | 2 => 7769
  | 3 => 7813

def recurringScratchCarry (l : Launch) (site : Fin 4) (entry : Fin 2)
    (ps rs base : Nat) : List (Nat × Value) :=
  let reg := recurringSaveInputs site
  [(reg.pageStride, b64 ps), (reg.rowStride, b64 rs), (reg.headBase, b64 base),
   (reg.slot, b64 entry.val), (pointerReloadBase site, b64 (pointerReloadAddress l site))]

/-- Live stack bases, slot, and cache layout operands before the recurring reloads. -/
def recurringScratchSaveInput (l : Launch) (site : Fin 4) (entry : Fin 2)
    (ps rs base : Nat) : List (Nat × Value) :=
  [(7295, b64 (l.localBase + 96)), (7294, b64 (l.localBase + 64))] ++
    recurringScratchCarry l site entry ps rs base

private def recurringScratchPageFacts (l : Launch) (site : Fin 4) (entry : Fin 2)
    (ps rs base : Nat) : List (Nat × Value) :=
  [((recurringScratchWord site false).base, b64 (l.localBase + 96 + 4 * entry.val)),
   (scratchOffsetReg site, b64 (4 * entry.val)), (7294, b64 (l.localBase + 64))] ++
    recurringScratchCarry l site entry ps rs base

private theorem recurringScratchPageAddressCore {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g ps rs base : Nat} (site : Fin 4) (entry : Fin 2) :
    Seg kernel [] l g 2 ((recurringScratchWord site false).pc - 2)
      (recurringScratchSaveInput l site entry ps rs base)
      (recurringScratchWord site false).pc (recurringScratchPageFacts l site entry ps rs base) := by
  have hStack := hp.localMemory.2.1
  have hLoc : l.localBase + 96 < 2 ^ 64 := by omega
  have hBound : l.localBase + 96 + 4 * entry.val < 2 ^ 64 := by have := entry.isLt; omega
  have hCore : Seg kernel [] l g 2 ((recurringScratchWord site false).pc - 2)
      (recurringScratchSaveInput l site entry ps rs base)
      (recurringScratchWord site false).pc (recurringScratchPageFacts l site entry ps rs base) := by
    fin_cases site <;> fin_cases entry <;> intro s hs <;>
      simp only [recurringScratchWord, recurringScratchSaveInput, recurringScratchPageFacts,
        recurringScratchCarry, recurringSaveInputs, scratchOffsetReg, pointerReloadBase,
        List.cons_append, List.nil_append, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]
        at hs ⊢ <;>
      seg_fp hs using
        norm_bits [Nat.mod_eq_of_lt hLoc, Nat.mod_eq_of_lt hBound]
  exact hCore

private def recurringScratchRowInput (l : Launch) (site : Fin 4) (entry : Fin 2)
    (page ps rs base : Nat) : List (Nat × Value) :=
  [(scratchOffsetReg site, b64 (4 * entry.val)), (7294, b64 (l.localBase + 64)),
   ((recurringScratchWord site false).destination, b64 page)] ++
    recurringScratchCarry l site entry ps rs base

private def recurringScratchRowFacts (l : Launch) (site : Fin 4) (entry : Fin 2)
    (page ps rs base : Nat) : List (Nat × Value) :=
  [((recurringScratchWord site true).base, b64 (l.localBase + 64 + 4 * entry.val)),
   ((recurringScratchWord site false).destination, b64 page)] ++
    recurringScratchCarry l site entry ps rs base

private theorem recurringScratchRowAddressCore {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g page ps rs base : Nat} (site : Fin 4) (entry : Fin 2) :
    Seg kernel [] l g 1 ((recurringScratchWord site false).pc + 1)
      (recurringScratchRowInput l site entry page ps rs base)
      (recurringScratchWord site true).pc
      (recurringScratchRowFacts l site entry page ps rs base) := by
  have hStack := hp.localMemory.2.1
  have hLoc : l.localBase + 64 < 2 ^ 64 := by omega
  have hBound : l.localBase + 64 + 4 * entry.val < 2 ^ 64 := by have := entry.isLt; omega
  have hCore : Seg kernel [] l g 1 ((recurringScratchWord site false).pc + 1)
      (recurringScratchRowInput l site entry page ps rs base)
      (recurringScratchWord site true).pc
      (recurringScratchRowFacts l site entry page ps rs base) := by
    fin_cases site <;> fin_cases entry <;> intro s hs <;>
      simp only [recurringScratchWord, recurringScratchRowInput, recurringScratchRowFacts,
        recurringScratchCarry, recurringSaveInputs, scratchOffsetReg, pointerReloadBase,
      List.cons_append, List.nil_append, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte] at hs ⊢ <;>
      seg_fp hs using
        norm_bits [Nat.mod_eq_of_lt hLoc, Nat.mod_eq_of_lt hBound]
  exact hCore

/-- An observed ordinary read cannot write a generic-proxy byte at its own ordinal. -/
theorem observedReadNoWrite {X : Execution} {i : EvId} {pc : Nat}
    {src dst : Acc} {bytes : List (Option Byte)} (hr : X.get i = some ⟨pc, .rd src bytes⟩) :
    ¬ X.Access i dst true := by
  rintro (⟨_, _, h⟩ | ⟨_, ⟨_, h⟩, _⟩ | ⟨_, _, _, h⟩)
  · cases h
  · cases Option.some.inj (hr.symm.trans h)
  · cases Option.some.inj (hr.symm.trans h)

/-- Register facts retained while loading both local metadata words and saving a pointer. -/
structure RecurringSaveFrame (site : Fin 4) (F : List (Nat × Value)) : Prop where
  page : ((kernel.code.drop ((recurringScratchWord site false).pc - 2)).take 2).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  pageFresh : ∀ pair ∈ F, pair.1 ≠ (recurringScratchWord site false).destination
  row : ((kernel.code.drop ((recurringScratchWord site false).pc + 1)).take 1).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true
  rowFresh : ∀ pair ∈ F, pair.1 ≠ (recurringScratchWord site true).destination
  save : ((kernel.code.drop (recurringSaveAddressPc site)).take 6).all
    (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index pw rw page row ps rs base : Nat}
    (site : Fin 4) (entry : Fin 2) (hPBefore : pw < index) (hRBefore : rw < index + 1)
    (hPage : page < 2 ^ 31) (hRow : row < 2 ^ 31) (hPS : ps < 2 ^ 64) (hRS : rs < 2 ^ 64)
    (hFit : sourceScratchPayload page row ps rs base < 2 ^ 64)
include hp hX site entry hPBefore hRBefore hPage hRow hPS hRS hFit

/-- The decoded page/row loads supply the pointer stored in the selected lane-private slot. -/
theorem recurringScratchSaveObservedInPrefixWithFrame {s : TState} {F : List (Nat × Value)}
    (hKeep : RecurringSaveFrame site F)
    (hs : At s ((recurringScratchWord site false).pc - 2)
      (recurringScratchSaveInput l site entry ps rs base ++ F)) {ending : Option TState}
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index (pointerSavePc site) ending)
    (hPageStore : X.get (g, pw) = some ⟨(recurringScratchWord site false).store,
      .wr (scratchReloadAccess l g (recurringScratchWord site false) entry) (b32 page).toBytes⟩)
    (hRowStore : X.get (g, rw) = some ⟨(recurringScratchWord site true).store,
      .wr (scratchReloadAccess l g (recurringScratchWord site true) entry) (b32 row).toBytes⟩)
    (hPageLast : ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((scratchReloadAccess l g (recurringScratchWord site false) entry).loc.at k) →
      j ≤ pw ∨ index ≤ j)
    (hRowLast : ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((scratchReloadAccess l g (recurringScratchWord site true) entry).loc.at k) →
      j ≤ rw ∨ index ≤ j) :
    X.get (g, index) = some ⟨(recurringScratchWord site false).pc,
      .rd (scratchReloadAccess l g (recurringScratchWord site false) entry)
        ((b32 page).toBytes.map some)⟩ ∧
    X.get (g, index + 1) = some ⟨(recurringScratchWord site true).pc,
      .rd (scratchReloadAccess l g (recurringScratchWord site true) entry)
        ((b32 row).toBytes.map some)⟩ ∧
    X.get (g, index + 2) = some ⟨pointerSavePc site,
      .wr (pointerSaveAccess l g site entry)
        (b64 (sourceScratchPayload page row ps rs base)).toBytes⟩ ∧
    ∃ u, At u (pointerSavePc site + 1) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 3)) ending := by
  let pOp := recurringScratchWord site false
  let rOp := recurringScratchWord site true
  have ⟨hCore, hsF⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨t, hPageCode, ht⟩ := recurringScratchPageAddressCore hp (g := g) site entry s
    (hs.mono hCore)
  have hPLo : 174 ≤ pOp.pc - 2 := by fin_cases site <;> decide
  have hPHi : pOp.pc - 2 + 2 ≤ 1906 := by fin_cases site <;> decide
  have hPSeq : ((kernel.code.drop (pOp.pc - 2)).take 1).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hT, hTF⟩ := loaderLinear (regs := F.map Prod.fst) hPLo hPHi hs.1 hKeep.page
    hPSeq hPageCode
  have htF := Epilogue.holdsSchedulerFrame hsF hTF (fun _ hm => List.mem_map_of_mem hm)
  have hPAddr : (scratchReloadAccess l g pOp entry).loc.addr =
      l.localBase + 96 + 4 * entry.val := by
    fin_cases site <;> simp [pOp, recurringScratchWord, scratchReloadAccess, kvLocalOffset,
      Nat.add_assoc]
  have hPT : At t pOp.pc [(pOp.base, b64 (scratchReloadAccess l g pOp entry).loc.addr)] := by
    rw [hPAddr]
    exact ht.mono ⟨ht.2.2.2.2.1, trivial⟩
  have hMore := hDemand.nonempty hRun
  have hAtPage := hRun.after_local_nonempty (run_rtg hT) hMore
  obtain ⟨_, hPageEvent⟩ := recurringScratchWordAccess hp site false entry hPT hAtPage hMore
  have hLatestPage : ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((scratchReloadAccess l g pOp entry).loc.at k) → j ≤ pw ∨ index < j := by
    intro k hk j dst ha hc
    rcases hPageLast k hk j dst ha hc with hOld | hLater
    · exact .inl hOld
    · have hNe : j ≠ index := by
        rintro rfl
        exact observedReadNoWrite hPageEvent ha
      exact .inr (by omega)
  obtain ⟨hPageRead, _, hPastPage⟩ := recurringScratchWordObservedInPrefix hp hX hPBefore hPage
    site false entry hPT hAtPage hMore hPageStore hLatestPage
  have hPagePc : pOp.pc ≤ pointerSavePc site := by fin_cases site <;> decide
  have hAfterPage := hDemand.advance hPageRead hPagePc
  let u := next (setReg t pOp.destination (b64 page))
  have hPFrame : ∀ pair ∈ recurringScratchPageFacts l site entry ps rs base,
      pair.1 ≠ pOp.destination := by
    fin_cases site <;> simp [pOp, recurringScratchPageFacts, recurringScratchWord,
      scratchOffsetReg, recurringScratchCarry, recurringSaveInputs, pointerReloadBase]
  have hU : At u (pOp.pc + 1) (recurringScratchRowInput l site entry page ps rs base) := by
    have hFull := ht.set (v := b64 page) hPFrame
    exact hFull.mono ⟨hFull.2.2.2.2.2.2.1, hFull.2.2.2.2.2.2.2.1, hFull.2.2.2.2.1,
      hFull.2.2.2.2.2.2.2.2⟩
  have huF : Holds u.regs F := (ht.mono htF).set (v := b64 page) hKeep.pageFresh |>.2.2.2.2.2
  obtain ⟨v, hRowCode, hv⟩ := recurringScratchRowAddressCore hp (g := g) site entry u hU
  have hRLo : 174 ≤ pOp.pc + 1 := by fin_cases site <;> decide
  have hRHi : pOp.pc + 1 + 1 ≤ 1906 := by fin_cases site <;> decide
  obtain ⟨hV, hVF⟩ := loaderLinear (regs := F.map Prod.fst) hRLo hRHi hU.1 hKeep.row rfl hRowCode
  have hvF := Epilogue.holdsSchedulerFrame huF hVF (fun _ hm => List.mem_map_of_mem hm)
  have hRAddr : (scratchReloadAccess l g rOp entry).loc.addr =
      l.localBase + 64 + 4 * entry.val := by
    fin_cases site <;> simp [rOp, recurringScratchWord, scratchReloadAccess, kvLocalOffset,
      Nat.add_assoc]
  have hRT : At v rOp.pc [(rOp.base, b64 (scratchReloadAccess l g rOp entry).loc.addr)] := by
    rw [hRAddr]
    exact hv.mono ⟨hv.2.2.2.2.1, trivial⟩
  have hMoreRow := hAfterPage.nonempty hPastPage
  have hAtRow := hPastPage.after_local_nonempty (run_rtg hV) hMoreRow
  obtain ⟨_, hRowEvent⟩ := recurringScratchWordAccess hp site true entry hRT hAtRow hMoreRow
  have hLatestRow : ∀ k < 4, ∀ j dst, X.Access (g, j) dst true →
      dst.Covers ((scratchReloadAccess l g rOp entry).loc.at k) → j ≤ rw ∨ index + 1 < j := by
    intro k hk j dst ha hc
    rcases hRowLast k hk j dst ha hc with hOld | hLater
    · exact .inl hOld
    · have hNoPage : j ≠ index := by
        rintro rfl
        exact observedReadNoWrite hPageEvent ha
      have hNoRow : j ≠ index + 1 := by
        rintro rfl
        exact observedReadNoWrite hRowEvent ha
      exact .inr (by omega)
  obtain ⟨hRowRead, _, hPastRow⟩ := recurringScratchWordObservedInPrefix hp hX hRBefore hRow
    site true entry hRT hAtRow hMoreRow hRowStore hLatestRow
  have hRowPc : rOp.pc ≤ pointerSavePc site := by fin_cases site <;> decide
  have hAfterRow := hAfterPage.advance hRowRead hRowPc
  have hRFrame : ∀ pair ∈ recurringScratchRowFacts l site entry page ps rs base,
      pair.1 ≠ rOp.destination := by
    fin_cases site <;> simp [rOp, recurringScratchRowFacts, recurringScratchWord,
      recurringScratchCarry, recurringSaveInputs, pointerReloadBase]
  have hPc : rOp.pc + 1 = recurringSaveAddressPc site := by fin_cases site <;> decide
  have hAt : At (next (setReg v rOp.destination (b64 row))) (recurringSaveAddressPc site)
      (recurringSaveAddressFacts l site entry page row ps rs base) := by
    rw [← hPc]
    have hFull := hv.set (v := b64 row) hRFrame
    have hIds : rOp.destination = (recurringSaveInputs site).row ∧
        pOp.destination = (recurringSaveInputs site).page := by fin_cases site <;> decide
    refine hFull.mono ?_
    exact ⟨hIds.2 ▸ hFull.2.2.2.2.2.2.1, hIds.1 ▸ hFull.2.2.2.2.1,
      hFull.2.2.2.2.2.2.2⟩
  have hW := ((hv.mono hvF).set (v := b64 row) hKeep.rowFresh).2.2.2.2.2
  have hWith := hAt.mono ((holds_append ..).mpr ⟨hAt.2.2.2.2, hW⟩)
  obtain ⟨hSave, u, hU, hTail⟩ :=
    recurringAddressSaveObservedWithFrame hp site entry (by omega) (by omega) hPS hRS hFit
      hKeep.save hWith hPastRow hAfterRow
  exact ⟨hPageRead, hRowRead, hSave, u, hU, by simpa only [Nat.add_assoc] using hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
