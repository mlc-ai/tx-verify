-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexOrdinal
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexRendezvous
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Clc.ClcExecution
import Lemmas.Step.WarpShfl

public section

/-! # A pending index butterfly keeps all its warp peers live -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- Every lane of a warp at an index butterfly is still participating and has the same
shuffle count. A peer cannot exit with the required two butterflies for each block. -/
theorem index_shuffle_peers {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Index.D} {extra second : Bool}
    (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hub : ¬ HasUb X)
    (hp : Frame.Pending L X g)
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.index d)))
    (hSite : d.site = (if second then .quad2 extra else .quad1 extra)) :
    ∀ h, SameWarp L g h → Frame.Pending L X h ∧
      (X.tr h).countP Execution.isShfl = Wg1Index.shuffleCount d := by
  let sound := fun h hh => (hs h hh).machine
  have hw : warpOf L g = 7 := RingRoleGeometry.of_trace hX hp.1 (sound g hp.1) hState
  have hIndexCount := Wg1Index.index_prefix_shuffle_count hpre hX sound hw le_rfl hState
  rw [List.take_length] at hIndexCount
  have hWarp (h : Nat) (hw' : SameWarp L g h) : warpOf L h = 7 := by
    have eq (a : Nat) : warpOf L a = a % L.block / 32 := by
      simp [warpOf, tidOf_eq hpre, hpre.block]
    rw [eq, ← hw'.2, ← eq, hw]
  obtain ⟨t, hgRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, hinv, hc, hOut⟩ := Frame.end_at hs hp.1 hgRun hState
  change Wg1Index.Inv P L g d at hinv
  have hBound : Wg1Index.shuffleCount d < 3 + 2 * totalBlocks d.len0 d.len1 := by
    have hBlock := hinv.block
    cases second <;> simp [Wg1Index.shuffleCount, hSite] <;> omega
  have hCountLe (h : Nat) (hh : SameWarp L g h) :
      (X.tr h).countP Execution.isShfl ≤ Wg1Index.shuffleCount d := by
    by_contra! hGt
    obtain ⟨i, hi⟩ := PTX.Step.exists_shflK
      (show Wg1Index.shuffleCount d + 1 ≤ (X.tr h).countP Execution.isShfl by omega)
    obtain ⟨pc, m, a, b, c, r, ok, he⟩ := hi.1
    rcases PTX.Step.shfl_lane_of_ready hX he hi (sameWarp_symm hh) with ⟨j, hj⟩ | hExit
    · have hG := PTX.Step.ShflK.lt_count hj
      rw [hIndexCount] at hG
      omega
    · obtain ⟨j, tag, hj, _⟩ := hExit
      exact hgRun.no_exit hj
  have hNoExit (h : Nat) (hh : SameWarp L g h) {i tag : Nat} :
      X.get (h, i) ≠ some ⟨tag, .exit⟩ := by
    intro he
    have hCount := Wg1Index.warp_seven_exit_count hpre hX sound (hWarp h hh) he
    have hSame : Wg1Index.eOf L h = Wg1Index.eOf L g := by
      have hCta : ctaOf L h = ctaOf L g := hh.1.2.2.symm
      simp only [Wg1Index.eOf, ctaidY, hCta]
    rw [hSame, ← hinv.len0, ← hinv.len1] at hCount
    have hTakeLe := (List.take_sublist i (X.tr h)).countP_le (p := Execution.isShfl)
    have hLe := hCountLe h hh
    omega
  intro h hh
  refine ⟨⟨hh.1.2.1, ?_, ?_⟩, ?_⟩
  · rintro ⟨_, _, hCancel⟩
    obtain ⟨i, sp, targets, _, hIssue, _⟩ := hX.clc.canceled_has_issue hCancel
    exact GlobalWrites.no_clc (i := i) (s := sp) (tg := targets) hX hIssue
  · intro tag hLast
    rw [List.getLast?_eq_getElem?] at hLast
    exact hNoExit h hh hLast
  · rw [← hIndexCount]
    exact (PTX.Step.shfl_count_eq hX hh (fun a ha _ hExited => by
      obtain ⟨_, _, hExit, _⟩ := hExited
      exact hNoExit a ha hExit)).symm

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
