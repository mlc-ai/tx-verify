-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Machine
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.StepsElect
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.StepsLens
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.StepsQ
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.StepsLoop
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The MMA warp's obligations

Every state of the machine satisfies its step obligation (`stepAt`): the site files prove them by
`site_cases`, one declaration per site or `Fin` family. A hand-back state (`leave s`) sits at an
event of the idle code and stops following the lane (`stepAt_leave`): warpgroup 1's idle code
follows it from there. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A hand-back state sits at an unguarded event of the idle code and stops. -/
theorem stepAt_leave (d : D) {s : IdleSite} (hs : d.site = .leave s) : (code P L g).StepAt d where
  site _ := by
    show ∃ ins, kernel.code[d.site.pc]? = some ins ∧ _
    rw [hs]
    cases s
    · exact ⟨_, Flow.code_2596, rfl, trivial⟩
    · exact ⟨_, Flow.code_2601, rfl, trivial⟩
    · exact ⟨_, Flow.code_2604, rfl, trivial⟩
    · exact ⟨_, Flow.code_3611, rfl, trivial⟩
  step _ _ _ _ _ := Or.inl (Or.inl (by simp only [code, succ, hs]))

/-- **Every state satisfies its step obligation.** -/
theorem stepAt (hp : Pre P L m) (d : D) : (code P L g).StepAt d := by
  cases hs : d.site with
  | elect => exact stepAt_elect hp d hs
  | loadTopk => exact stepAt_loadTopk hp d hs
  | loadExtra => exact stepAt_loadExtra hp d hs
  | trap => exact stepAt_trap d hs
  | qLoad k => exact stepAt_qLoad d ⟨k, hs⟩
  | qArrive => exact stepAt_qArrive d hs
  | qWait => exact stepAt_qWait d hs
  | qFence => exact stepAt_qFence d hs
  | qCopy k => exact stepAt_qCopy d ⟨k, hs⟩
  | qCopyCommit => exact stepAt_qCopyCommit d hs
  | qCopyWait => exact stepAt_qCopyWait d hs
  | qCopyFence => exact stepAt_qCopyFence d hs
  | kvWait => exact stepAt_kvWait d hs
  | kvFence => exact stepAt_kvFence d hs
  | qk k => exact stepAt_qk d ⟨k, hs⟩
  | qkCommit => exact stepAt_qkCommit d hs
  | soWait => exact stepAt_soWait d hs
  | soFence => exact stepAt_soFence d hs
  | pv k => exact stepAt_pv d ⟨k, hs⟩
  | pvCommit => exact stepAt_pvCommit d hs
  | outBar => exact stepAt_outBar d hs
  | exit => exact stepAt_exit d hs
  | leave s => exact stepAt_leave d hs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
