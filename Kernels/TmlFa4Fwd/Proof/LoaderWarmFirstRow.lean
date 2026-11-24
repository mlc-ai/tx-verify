-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringIndexSeed
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageRefresh
import Kernels.TmlFa4Fwd.Flow.Code.Part014

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

private theorem warmLaneSeedCore {l : Launch} {g : Nat} (slot : Fin 2) (more : Bool) :
    Seg kernel [] l g 2 921 [(7175, b32 slot.val), (775, .pred more)] 923
      [(8, .pred more), (1964, b32 (64 * slot.val))] := by
  fin_cases slot <;> cases more <;> intro s hs <;> seg_fp hs using rfl

private theorem warmFirstAddRow {l : Launch} {g tile tid : Nat}
    (hTile : 128 * tile + 127 < 2 ^ 31) :
    Seg kernel [] l g 1 928 [(1968, b32 (primingLaneRow 0 tid)), (1118, b32 (128 * tile))]
      929 [(1969, b32 (primingLaneRow tile tid))] := by
  have hOffset : primingLaneRow 0 tid < 64 := by
    simp [primingLaneRow, kvCopyColumn]
    have h0 := Nat.mod_lt (tid / 8) (by decide : 0 < 8)
    have h1 := Nat.mod_lt tid (by decide : 0 < 8)
    omega
  have hSum : primingLaneRow 0 tid + 128 * tile = primingLaneRow tile tid := by
    unfold primingLaneRow
    omega
  have hOff32 : primingLaneRow 0 tid < 2 ^ 32 := by omega
  have hBase32 : 128 * tile < 2 ^ 32 := by omega
  have hRow32 : primingLaneRow tile tid < 2 ^ 32 := by rw [← hSum]; omega
  intro s hs
  seg_fp hs using
    simp only [b32, truncBits_ofNat hOff32 (by decide), truncBits_ofNat hBase32 (by decide),
      ← BitVec.ofNat_add, hSum, truncBits_ofNat hRow32 (by decide)]

variable {l : Launch} {g tile tid : Nat} (hTile : 128 * tile + 127 < 2 ^ 31) (hTid : tid < 512)
include hTile hTid

/-- Each warm scratch slot computes the same lane row before adding its own offset. -/
theorem warmPageIndexRunFromSlot (slot : Fin 2) (more : Bool) {s : TState} {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop 921).take (929 - 921)).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 921 ([(1118, b32 (128 * tile)), (1061, b32 tid),
      (7175, b32 slot.val), (775, .pred more)] ++ F)) :
    ∃ u, run kernel Assumptions.all l g 8 s = some u ∧
      At u 929 ([(1969, b32 (primingLaneRow tile tid)), (1964, b32 (64 * slot.val)),
        (7175, b32 slot.val), (8, .pred more), (1118, b32 (128 * tile)),
        (1119, b32 (8 * (tid % 8)))] ++ F) := by
  obtain ⟨a, ha, hA⟩ := warmLaneSeedCore (l := l) (g := g) slot more s
    (hs.mono ⟨hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.1, trivial⟩)
  obtain ⟨_, hSeedKeep⟩ := loaderLinear (regs := [1118, 1061, 7175]) (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) ha
  have hTidA := (hSeedKeep 1061 (by simp)).trans hs.2.2.2.2.2.1
  have hBaseA := (hSeedKeep 1118 (by simp)).trans hs.2.2.2.2.1
  have hSlotA := (hSeedKeep 7175 (by simp)).trans hs.2.2.2.2.2.2.1
  obtain ⟨b, hb, hB⟩ := recurringLaneOffsetWithColumnCore (l := l) (g := g) hTid 0 a
    (hA.mono ⟨hTidA, trivial⟩)
  change At b 928 [(1968, b32 (primingLaneRow 0 tid)), (1119, b32 (8 * (tid % 8)))] at hB
  let keep := [1118, 1964, 7175, 8]
  obtain ⟨_, hbKeep⟩ := loaderLinear (regs := keep) (by decide) (by decide) hA.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hb
  have hBaseB := (hbKeep 1118 (by simp [keep])).trans hBaseA
  obtain ⟨u, hu, hU⟩ := warmFirstAddRow (l := l) (g := g) hTile b
    (hB.mono ⟨hB.2.2.2.2.1, hBaseB, trivial⟩)
  have hAll := run_comp (run_comp ha hb) hu
  obtain ⟨hRun, hFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    hKeep (by set_option maxRecDepth 100000 in kernel_rfl) hAll
  obtain ⟨_, huKeep⟩ := loaderLinear (regs := 1119 :: keep) (by decide) (by decide) hB.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  exact ⟨u, hRun, hU.mono ⟨hU.2.2.2.2.1,
    (huKeep 1964 (by simp [keep])).trans ((hbKeep 1964 (by simp [keep])).trans hA.2.2.2.2.2.1),
    (huKeep 7175 (by simp [keep])).trans ((hbKeep 7175 (by simp [keep])).trans hSlotA),
    (huKeep 8 (by simp [keep])).trans ((hbKeep 8 (by simp [keep])).trans hA.2.2.2.2.1),
    (huKeep 1118 (by simp [keep])).trans hBaseB,
    (huKeep 1119 (by simp)).trans hB.2.2.2.2.2.1,
    holdsSchedulerFrame ((holds_append ..).mp hs.2.2.2.2).2 hFrame
      (fun _ hm => List.mem_map_of_mem hm)⟩⟩

/-- The first warm iteration reaches the first slot and retains the inner-loop seed. -/
theorem warmFirstIndexRunWithRowSeed {s : TState} {F : List (Nat × Value)}
    (hKeep₁ : ((kernel.code.drop 917).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hKeep₂ : ((kernel.code.drop 921).take 8).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 917 ([(1116, b32 tile), (7174, b32 0), (1061, b32 tid)] ++ F)) :
    ∃ u, run kernel Assumptions.all l g 12 s = some u ∧
      At u 929 ([(1969, b32 (primingLaneRow tile tid)), (1964, b32 0), (7175, b32 0),
        (8, .pred true), (1118, b32 (128 * tile)), (1119, b32 (8 * (tid % 8)))] ++ F) := by
  obtain ⟨seed, hSeed, hAt⟩ := warmPageTileSeedCore (l := l) (g := g)
    (show 0 ≤ tile by omega) (by omega) s (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩)
  have hKeep : ((kernel.code.drop 917).take 4).all
      (fun ins => (1061 :: F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) =
      true := by
    apply List.all_eq_true.mpr
    intro ins hm
    simp only [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, List.all_eq_true.mp hKeep₁ ins hm⟩
    have hTidSafe : ((kernel.code.drop 917).take 4).all
        (fun i => !(writesRegs i.op).contains 1061) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    exact List.all_eq_true.mp hTidSafe ins hm
  obtain ⟨hSeedA, hFrame⟩ := loaderLinear (regs := 1061 :: F.map Prod.fst)
    (by decide) (by decide) hs.1 hKeep (by set_option maxRecDepth 100000 in kernel_rfl) hSeed
  have hTidS := (hFrame 1061 (by simp)).trans hs.2.2.2.2.2.2.1
  have hf := holdsSchedulerFrame ((holds_append ..).mp hs.2.2.2.2).2 hFrame
    (fun r hm => .tail 1061 (List.mem_map_of_mem hm))
  have hInput : At seed 921 ([(1118, b32 (128 * tile)), (1061, b32 tid),
      (7175, b32 (0 : Fin 2).val), (775, .pred true)] ++ F) :=
    hAt.mono ⟨by simpa using hAt.2.2.2.2.1, hTidS, hAt.2.2.2.2.2.1, hAt.2.2.2.2.2.2.1, hf⟩
  obtain ⟨u, hu, hU⟩ := warmPageIndexRunFromSlot hTile hTid 0 true hKeep₂ hInput
  exact ⟨u, run_comp hSeedA hu, by simpa using hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
