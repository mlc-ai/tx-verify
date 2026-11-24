-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Proof.Correction.StepsEnd
import Kernels.TmlFa4Fwd.Proof.Correction.StepsFinal
import Kernels.TmlFa4Fwd.Proof.Correction.StepsFinalData
import Kernels.TmlFa4Fwd.Proof.Correction.StepsFinalMax
import Kernels.TmlFa4Fwd.Proof.Correction.StepsFinalStore
import Kernels.TmlFa4Fwd.Proof.Correction.StepsLse
import Kernels.TmlFa4Fwd.Proof.Correction.StepsReq
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRescale
import Kernels.TmlFa4Fwd.Proof.Correction.StepsRound
import Kernels.TmlFa4Fwd.Proof.Correction.StepsScale
import Kernels.TmlFa4Fwd.Proof.Correction.StepsScanFirst
import Kernels.TmlFa4Fwd.Proof.Correction.StepsScanLoop
import Kernels.TmlFa4Fwd.Proof.Correction.StepsScanLoop2
import Kernels.TmlFa4Fwd.Proof.Correction.StepsScanSecond
import Kernels.TmlFa4Fwd.Proof.Correction.StepsSelect
import Kernels.TmlFa4Fwd.Proof.Correction.StepsStart
import Kernels.TmlFa4Fwd.Proof.Correction.StepsTiles
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

/-! # The correction warps' machine steps at every state

`stepAt`: the step obligation of every state of the correction machine, from the families of
`Steps*.lean` (each by `site_cases`), and the states at a sub-step their site does not have
(`stepAt_junk`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **Every state of the correction machine obeys its step obligation.** -/
theorem stepAt (hp : Pre p L m) (hg : g < L.threads) (d : D) : (code p L g).StepAt d := by
  by_cases hfst : ∃ st j h, d.site = .fst st j h
  · exact stepAt_fst hp hg d hfst
  by_cases hw : ∃ st c, d.site = .rldw st c
  · by_cases h1 : d.k = 1
    · exact stepAt_rldw hp hg d h1 hw
    by_cases h0 : d.k = 0
    · exact stepAt_rldw0 hp hg d h0 hw
    obtain ⟨st, c, hs⟩ := hw
    exact stepAt_junk (by simp [hs, Site.midOk, h0, h1])
  by_cases hk : d.k = 0
  swap
  · refine stepAt_junk ?_
    rintro (h | h)
    · exact hk h
    · obtain ⟨s, v, k⟩ := d
      cases s <;> simp_all [Site.midOk]
  obtain ⟨s, v, k⟩ := d
  simp only at hk
  subst hk
  cases s with
  | setmax | bar1 | arr _ => exact stepAt_start hp hg _ rfl (by simp)
  | word k | down k | total k =>
    cases k
    · exact stepAt_scan_first hp hg _ rfl (by simp)
    · exact stepAt_scan_loop hp hg _ rfl (by simp)
    · exact stepAt_scan_second hp hg _ rfl (by simp)
    · exact stepAt_scan_loop2 hp hg _ rfl (by simp)
  | up k j =>
    cases k
    · exact stepAt_scan_first hp hg _ rfl (by simp)
    · exact stepAt_scan_loop hp hg _ rfl (by simp)
    · exact stepAt_scan_second hp hg _ rfl (by simp)
    · exact stepAt_scan_loop2 hp hg _ rfl (by simp)
  | vote _ | pre _ => exact stepAt_select hp hg _ rfl (by simp)
  | tiles l =>
    cases l
    · exact stepAt_tiles hp hg _ rfl rfl
    · exact stepAt_select hp hg _ rfl (by simp)
  | q0 | q1 | uk | nb _ | free => exact stepAt_req hp hg _ rfl (by simp)
  | rbar _ | rvote _ | rwait _ | rarr _ _ => exact stepAt_round hp hg _ rfl (by simp)
  | rscale st => exact stepAt_scale hp st _
  | rld _ _ | rst _ _ => exact stepAt_rld hp hg _ rfl (by simp)
  | rldw _ _ => exact absurd ⟨_, _, rfl⟩ hw
  | fst _ _ _ => exact absurd ⟨_, _, _, rfl⟩ hfst
  | fmax st => exact stepAt_fmax hp st _
  | farr0 | fbar _ | fsum _ | farr _ | fw _ _ | fence _ =>
    exact stepAt_final hp hg _ rfl (by simp)
  | fdone st k =>
    fin_cases st <;> fin_cases k
    · exact stepAt_final hp hg _ rfl (by simp)
    · exact stepAt_final hp hg _ rfl (by simp)
    · exact stepAt_final hp hg _ rfl (by simp)
    · exact stepAt_lse hp hg _ rfl (by simp)
  | lse _ => exact stepAt_lse hp hg _ rfl (by simp)
  | fld _ _ | fwl _ _ => exact stepAt_fld hp hg _ rfl (by simp)
  | wend _ | barEnd _ | exit _ => exact stepAt_ends hp hg _ rfl (by simp)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
