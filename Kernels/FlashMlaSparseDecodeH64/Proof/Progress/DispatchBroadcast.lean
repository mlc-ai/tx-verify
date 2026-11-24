-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.RegisterBlocker
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressStartupShuffle
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueShuffleTrace
import Lemmas.Step.WarpShfl

public section

/-! # Progress at the dispatch broadcast of warpgroup one -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

/-- A pending dispatch descends to a pre-dispatch peer unless the complete warp can issue. -/
theorem pending_dispatch_earlier {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g .head) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g .head := by
  have hX := hmax.1
  have hSafe := Safety.no_unsafe_of_tracked hpre hX hs ht
  have hub : ¬ HasUb X := fun h => hSafe (.inl h)
  let sound := fun h hh => (hs h hh).machine
  obtain ⟨hLen, hGroup⟩ := PrologueRoleTrace.head_position hpre hX sound le_rfl hp.2
  have h3 : 3 < (X.tr g).length := by omega
  have hr : X.get (g, 3) = some (X.tr g)[3] := List.getElem?_eq_getElem h3
  have hCount := PrologueShuffleTrace.head_prefix_count hpre hX sound hr hGroup
  rw [← hLen, List.take_length] at hCount
  have hBefore (h : Nat) (s : Site) : priority P L h (.prologue s) < priority P L g .head := by
    simp only [priority]
    omega
  by_contra hEarlier
  apply hmax.not_grows (startup_shuffle_extension hpre hs hX hp.1.1 hub .dispatch ?_)
  intro h hw
  have hg' : wgOf L h = 1 := by
    have hWarp : warpOf L h = warpOf L g := by
      simpa only [warpOf, tidOf_eq hpre, hpre.block] using hw.2.symm
    have hEq := congrArg (· / 4) hWarp
    simp only [warpOf, Nat.div_div_eq_div_mul] at hEq
    change wgOf L h = wgOf L g at hEq
    exact hEq.trans hGroup
  have hLimit : (X.tr h).length ≤ 4 := by
    by_contra! hMore
    have he : X.get (h, 4) = some (X.tr h)[4] := List.getElem?_eq_getElem hMore
    have hK := PrologueShuffleTrace.head_ordinal hpre hX sound he hg'
    obtain ⟨⟨_, _, _, _, _, _, _, he'⟩, _⟩ := id hK
    have hw' : SameWarp L h g := ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩
    rcases PTX.Step.shfl_lane_of_ready hX he' hK hw' with ⟨j, hj⟩ | ⟨j, _, hj, _⟩
    · have hGt : 2 < (X.tr g).countP Execution.isShfl := PTX.Step.ShflK.lt_count hj
      omega
    · obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp.1
      exact hRun.no_exit hj
  have hPending := PrologueShuffleTrace.dispatch_prefix_pending hpre hX sound hw.1.2.1 hg'
    hLimit (fun _ _ _ => GlobalWrites.no_clc hX)
  rcases PrologueShuffleTrace.dispatch_prefix_tail hpre hX sound hg' hLimit with
    ⟨s, hState⟩ | ⟨hState, tag, inc, n, inst, he⟩
  · exact (hEarlier ⟨h, .prologue s, ⟨hPending, hState⟩, hBefore h s⟩).elim
  refine ⟨hPending, ⟨fun tag' k he' _ => ?_⟩, hState⟩
  cases Option.some.inj (he.symm.trans he')
  by_contra hWait
  obtain ⟨z, s, hZ, _⟩ := waiting_register_prologue hpre hX hs ht he hWait
  exact hEarlier ⟨z, .prologue s, hZ, hBefore z s⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
