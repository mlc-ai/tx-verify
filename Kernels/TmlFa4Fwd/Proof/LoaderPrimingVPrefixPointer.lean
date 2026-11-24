-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixSaved
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVFirstCopy
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) {e : Event}
    (he : X.get (warpLane l g src, j) = some e) (hLate : 804 < e.pc)
include hp hX hg hw hl writes hCTA he hLate

/-- A live V prefix reloads the two exact halves of its first saved pointer and
keeps the K-prepared mask for the first V vector. -/
theorem loaderPrimingVFirstPointerAndSavedOfActiveEvent (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let tile := Mma.trips p batch co.1 - 1
      let thread := warpLane l g src
      let tid := 32 * warpIndex l g + src
      let row := primingLaneRow tile tid
      let base := primingVRowPointer p batch (co.2 / 6) row
      ∃ pos ≤ j, ∃ s ending,
        At s 805 (primingVReloadWords 0 base ++ vPacketAfterKFrame p l g batch (co.2 / 6)
          tile (fun _ => vPrimingResidual p batch co.1) src) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 32 ∧
        ∃ read a data, pos = read + 2 ∧ X.get (thread, read) = some ⟨804, .rd a data⟩ ∧
          PrimingCellValue X thread read 799 (sourceScratchAccess l thread 1)
            (b64 (primingVRowPointer p batch (co.2 / 6) (row + 64))).toBytes := by
  obtain ⟨batch, hb, hLo, hHi, _, index, hOrder, s, ending, hs, hr, hRank, hStored⟩ :=
    loaderPrimingVSavedOfActiveEvent hp hX hg hw hl writes hCTA he (by omega) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let tile := Mma.trips p batch co.1 - 1
  let thread := warpLane l g src
  let tid := 32 * warpIndex l g + src
  let row := primingLaneRow tile tid
  let base := primingVRowPointer p batch (co.2 / 6) row
  let F := vPacketAfterKFrame p l g batch (co.2 / 6) tile
    (fun _ => vPrimingResidual p batch co.1) src
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by unfold co; unfold Params.heads at hHead; omega
  have hPage := primingScratchPageBound hp (row := row) hb
  obtain ⟨hEq, hFit, _⟩ := sourceScratchPayload_live hp 1 hPage (Nat.mod_lt row (by decide)) hh
  have hBase : base < 2 ^ 64 := by rw [hEq] at hFit; exact hFit
  have hSeed : At s 803 [(1089, b32 (vPrimingResidual p batch co.1))] :=
    hs.mono ⟨holds_lookup hs.2.2.2.2 rfl, trivial⟩
  have hSavedFrame : Holds s.regs ((7292, b64 l.localBase) :: F) := by
    exact ⟨holds_lookup hs.2.2.2.2 rfl, hs.2.2.2.2⟩
  obtain ⟨u, hu, hU⟩ := primingVFirstReloadPrep (g := thread) s hSeed
  obtain ⟨huA, hKeep⟩ := loaderLinear (regs := ((7292, b64 l.localBase) :: F).map Prod.fst)
    (by decide) (by decide) hs.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have huAt : At u 804 ((7292, b64 l.localBase) :: F) :=
    hU.mono (holdsSchedulerFrame hSavedFrame hKeep (fun _ hm => List.mem_map_of_mem hm))
  have hPending : PrefixDemand X thread index 804 ending := .inr ⟨j, e, hOrder, hLate, he⟩
  have huRun := hr.after_local_nonempty (run_rtg huA) (hPending.nonempty hr)
  have hAddr : l.localBase + (primingVPointerReload 0).offset < 2 ^ 64 := by
    have := hp.localMemory.2.1
    change l.localBase + 0 < 2 ^ 64
    omega
  have hAlign : (l.localBase + (primingVPointerReload 0).offset) % 8 = 0 := by
    change (l.localBase + 0) % 8 = 0
    have := hp.localMemory.1
    omega
  obtain ⟨w, hBefore, hwAt, hLatest⟩ := hStored (0 : Fin 2)
  have hStore : X.Writes (thread, w) ((primingVPointerReload 0).cell thread l.localBase)
      (b64 base).toBytes := ⟨799, hwAt⟩
  obtain ⟨v, hv, hFrame, hvRun, hRead0, hRead1⟩ :=
    (primingVPointerReload 0).observedInPrefix hX (by decide) Flow.code_804
      hAddr hAlign (by decide) hBase hBefore huAt
      (by
        intro pair hPair
        have hAudit : (F.map Prod.fst).all (fun r => decide (r ≠ 1927 ∧ r ≠ 1928)) = true := by
          set_option maxRecDepth 100000 in kernel_rfl
        exact of_decide_eq_true (List.all_eq_true.mp hAudit _ (List.mem_map_of_mem hPair)))
      (bound := 804) (by decide) huRun hPending hStore hLatest
  have advance {i : Nat} {event : Event} (hi : X.get (thread, i) = some event)
      (hSite : event.pc = 804) (hBefore : i ≤ j) : i + 1 ≤ j := by
    by_contra! hEarlier
    have hEq : i = j := by omega
    rw [hEq] at hi
    obtain rfl := Option.some.inj (he.symm.trans hi)
    omega
  have hNext := advance hRead0 rfl hOrder
  have hPos := advance hRead1 rfl hNext
  have hCount0 := Flow.countP_take_succ_false (p := Execution.isShfl) hRead0 rfl
  have hCount1 := Flow.countP_take_succ_false (p := Execution.isShfl) hRead1 rfl
  have hCount : ((X.tr thread).take (index + 2)).countP Execution.isShfl =
      primingSearchShuffleCount batch + 32 := by
    rw [show index + 2 = index + 1 + 1 by omega, hCount1, hCount0, hRank]
  exact ⟨batch, hb, hLo, hHi, _, hPos, v, ending,
    hv.mono ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.1, hFrame⟩, hvRun, hCount,
    index, _, _, rfl, hRead0, hStored 1⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
