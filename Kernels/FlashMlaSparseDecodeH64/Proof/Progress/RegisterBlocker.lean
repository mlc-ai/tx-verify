-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Lemmas.Step.SetMaxNReg
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RegisterRequestTrace
import Lemmas.Step.WarpLanes

public section

/-! # A missing register participant is still in the launch prologue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A warp waiting at its first register request has a pending peer before hand-off. -/
theorem waiting_register_prologue {g tag n inst : Nat} {inc : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : SetMaxNReg.Request X (g, (X.tr g).length - 1) tag inc n inst)
    (hwait : ¬ Ready L X (g, (X.tr g).length - 1)) :
    ∃ h s, PendingState P L X h (.prologue s) ∧ priority P L h (.prologue s) ≤ 99 := by
  have hSafe := Safety.no_unsafe_of_tracked hpre hX hs ht
  have hg := Frame.lt_of_get hX hr
  obtain ⟨lane, hLane, hMissing⟩ := Step.missing_member_lane hSafe hr hwait
  let h := warpLane L g lane
  obtain ⟨hWarp, hLaneEq⟩ := Step.sameWarp_lane (by rw [hpre.block]) hg hLane
  have hh : h < L.threads := hWarp.1.2.1
  have hNo (j tag' : Nat) (inc' : Bool) (n' inst' : Nat) :
      ¬ SetMaxNReg.Request X (h, j) tag' inc' n' inst' := by
    intro he
    exact (hMissing h hh hWarp hLaneEq).2 j tag' inc' n' inst' he
      ((RegisterRequestTrace.request_payload hpre hX hs ht he).1.trans
        (RegisterRequestTrace.request_payload hpre hX hs ht hr).1.symm)
  have hCount := RegisterRequestTrace.count_eq_zero_of_no_request hNo
  have hp : Frame.Pending L X h := by
    refine ⟨hh, ?_, ?_⟩
    · rintro ⟨_, _, hCanceled⟩
      obtain ⟨i, sp, targets, _, hi, _⟩ := hX.clc.canceled_has_issue hCanceled
      exact GlobalWrites.no_clc (i := i) (s := sp) (tg := targets) hX hi
    · intro tag' hLast
      rw [List.getLast?_eq_getElem?] at hLast
      have hOrd := RegisterRequestTrace.exit_ordinal hX hs ht hLast
      change SetMaxNReg.ordinal X (h, (X.tr h).length - 1) = 1 at hOrd
      have hLe := (List.take_sublist ((X.tr h).length - 1) (X.tr h)).countP_le
        (p := SetMaxNReg.isRequest)
      change SetMaxNReg.ordinal X (h, (X.tr h).length - 1) ≤ _ at hLe
      rw [hOrd, hCount] at hLe
      omega
  obtain ⟨d, hd⟩ := pending_followed hpre hX hs ht hp
  obtain ⟨s, rfl⟩ := RegisterRequestTrace.prologue_of_missing_request hX
    (hs h hh).machine hh hd hNo
  refine ⟨h, s, ⟨hp, hd⟩, ?_⟩
  cases s <;> simp only [priority, prologueRank] <;> omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
