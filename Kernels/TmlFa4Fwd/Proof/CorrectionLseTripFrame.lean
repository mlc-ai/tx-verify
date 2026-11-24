-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseReadyPrefix
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Lemmas.Flow.Footprint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction

open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue

noncomputable section

/-- The LSE address frame before the selected tile is scaled by 256. -/
def lseTripAddressFacts (p : Params) (l : Launch) (g batch head tile : Nat) :
    List (Nat × Value) :=
  [(7276, b32 tile), (1635, b32 (p.qLength batch)), (1613, b32 (rowOf l g)),
    (1634, b32 (p.qOffset batch)), (9605, b64 head), (7501, b64 p.lseStride),
    (7500, b64 p.lseBase)]

private def tripAddressRegs : List Nat := [7276, 1635, 1613, 1634, 9605, 7501, 7500]

private theorem tripAddressCode {pc : Nat} {i : Instr} (hLo : 7960 ≤ pc) (hHi : pc < 7985)
    (hc : kernel.code[pc]? = some i) :
    i.guard = none ∧ i.op.isLocal = true ∧ schedulerFallsThrough i.op = true ∧
      ∀ r ∈ tripAddressRegs, r ∉ writesRegs i.op := by
  have hSlice : ((kernel.code.drop 7960).take 25).all (fun ins =>
      ins.guard.isNone && ins.op.isLocal && schedulerFallsThrough ins.op &&
      tripAddressRegs.all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hm : i ∈ (kernel.code.drop 7960).take 25 := by
    apply List.mem_of_getElem? (i := pc - 7960)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
  have h := List.all_eq_true.mp hSlice i hm
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, fun r hr => by simpa using List.all_eq_true.mp h.2 r hr⟩

private theorem keepScaledTile {pc : Nat} {i : Instr} (hLo : 7971 ≤ pc) (hHi : pc < 7985)
    (hc : kernel.code[pc]? = some i) : 5967 ∉ writesRegs i.op := by
  have hSlice : ((kernel.code.drop 7971).take 14).all
      (fun ins => !(writesRegs ins.op).contains 5967) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hm : i ∈ (kernel.code.drop 7971).take 14 := by
    apply List.mem_of_getElem? (i := pc - 7971)
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]
  simpa using List.all_eq_true.mp hSlice i hm

private theorem scaleSelectedTile {l : Launch} {g tile : Nat} (hTile : 256 * tile < 2 ^ 32) :
    Seg kernel Assumptions.all l g 1 7970 [(7276, b32 tile)] 7971 [(5967, b32 (256 * tile))] := by
  have hSmall : tile < 2 ^ 32 := by omega
  intro t ht
  seg_fp ht using norm_bits [Nat.mul_comm tile 256]

/-- The actual post-UsedK local steps establish the same LSE address frame for every
value of the key-length word for which the lane reaches a later event. -/
theorem cutLseTripAddress {p : Params} {l : Launch} {g batch head tile : Nat}
    {s : TState} {target : Event} {events : List Event} {visits : List Visit}
    (hTile : 256 * tile < 2 ^ 32) (hLate : 7985 < target.pc)
    (hs : At s 7960 (lseTripAddressFacts p l g batch head tile))
    (hw : Walk kernel Assumptions.all l g s events visits) (he : target ∈ events) :
    ∃ u tail, At u 7985 (lseFootprintEntryFacts p l g batch head tile) ∧
      Walk kernel Assumptions.all l g u events tail := by
  let F := lseTripAddressFacts p l g batch head tile
  have hRegs : ∀ rv ∈ F, rv.1 ∈ tripAddressRegs := by
    intro rv hm
    have hr := List.mem_map_of_mem (f := Prod.fst) hm
    simpa [F, lseTripAddressFacts, tripAddressRegs] using hr
  have go {t : TState} {events : List Event} {vs : List Visit}
      (hw : Walk kernel Assumptions.all l g t events vs) (he : target ∈ events)
      (hLo : 7960 ≤ t.pc) (hHi : t.pc ≤ 7985) (ht : At t t.pc F)
      (hRow : 7971 ≤ t.pc → t.regs 5967 = some (b32 (256 * tile))) :
      ∃ u tail, At u 7985 (lseFootprintEntryFacts p l g batch head tile) ∧
        Walk kernel Assumptions.all l g u events tail := by
    have hAtExit {t : TState} (ht : At t t.pc F) (heq : t.pc = 7985)
        (hRow : t.regs 5967 = some (b32 (256 * tile))) :
        At t 7985 (lseFootprintEntryFacts p l g batch head tile) := by
      have hHold := ht.2.2.2.2
      rw [← heq]
      exact ht.mono ⟨hHold.2.1, hRow, hHold.2.2⟩
    induction hw with
    | stop => simp at he
    | @tau t u es vs hStep hWalk ih =>
      by_cases hend : t.pc = 7985
      · exact ⟨t, _, hAtExit ht hend (hRow (by omega)), .tau hStep hWalk⟩
      have hOff : t.pc ∉ Assumptions.swExp2Sites := by
        simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
        omega
      obtain ⟨i, hc, hFault, hSource⟩ := correctionTauFrame hOff hStep
      obtain ⟨hGuard, _, hFall, hNoWrite⟩ := tripAddressCode hLo (by omega) hc
      rcases hSource with ⟨_, hSkip⟩ | ⟨_, _, hFrame⟩
      · rw [hGuard] at hSkip
        cases hSkip
      have hPc : u.pc = t.pc + 1 := by
        have h := hFrame.pc
        cases hop : i.op <;> simp_all [schedulerFallsThrough, nextPc, BrxTarget]
      have hu : At u u.pc F := ⟨rfl, hFrame.sub.trans ht.2.1,
        hFrame.acc.trans ht.2.2.1, hFrame.fault.trans hFault,
        holdsSchedulerFrame ht.2.2.2.2 (fun r hr => hFrame.regs r (hNoWrite r hr)) hRegs⟩
      have hKeep (hl : 7971 ≤ u.pc) : u.regs 5967 = some (b32 (256 * tile)) := by
        by_cases hScale : t.pc = 7970
        · have hs' : At t 7970 [(7276, b32 tile)] := hScale ▸ ht.mono ⟨ht.2.2.2.2.1, trivial⟩
          obtain ⟨v, hv, hvAt⟩ := (scaleSelectedTile hTile).apply hs'
          have hOne : run kernel Assumptions.all l g 1 t = some u := by
            simp [run, tauStep_iff.mpr hStep]
          obtain rfl := Option.some.inj (hOne.symm.trans hv)
          exact hvAt.2.2.2.2.1
        · exact (hFrame.regs _ (keepScaledTile (by omega) (by omega) hc)).trans (hRow (by omega))
      exact ih he (by omega) (by omega) hu hKeep
    | @ev t u e es vs hEvent hWalk ih =>
      by_cases hend : t.pc = 7985
      · exact ⟨t, _, hAtExit ht hend (hRow (by omega)), .ev hEvent hWalk⟩
      obtain ⟨i, hc, hLocal, _⟩ := estep_event_source hEvent
      rw [(tripAddressCode hLo (by omega) hc).2.1] at hLocal
      cases hLocal
    | @last t e hEvent =>
      obtain rfl := List.mem_singleton.mp he
      have hPc := estep_source_pc hEvent
      omega
  exact go hw he (by rw [hs.1]) (by rw [hs.1]; decide) ⟨rfl, hs.2⟩
    (fun h => by rw [hs.1] at h; omega)

end
end PTX.Kernels.TmlFa4Fwd.Correction
