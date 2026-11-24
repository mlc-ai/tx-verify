-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.Correction.Ref
public import Kernels.TmlFa4Fwd.Proof.Correction.RefSucc
import Kernels.TmlFa4Fwd.Proof.Correction.RefSuccFinal
import Kernels.TmlFa4Fwd.Proof.Correction.RefSuccRound
import Kernels.TmlFa4Fwd.Proof.Correction.RefSuccScan

@[expose] public section

/-! # The successors of the correction machine's states

`succ_cases`: every step of the correction machine stays at its state (a failed poll), moves to
the next element of a vector store, or moves to a listed successor of its site (`nexts`) at the
successor's sub-step; in the last case it keeps the rounds' values (the counter, the used-K
length, the scan) when it lands in the rounds or the final stage, unless it is the entry or the
end of a round, and it keeps the row sums when it lands in the final stage, unless it reads a row
sum. One theorem per family of sites (`RefSucc*.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {g : Nat}

/-- **Every step of the correction machine** stays (a failed poll), moves to the next element of a
vector store, or moves to a listed successor with the step facts. -/
theorem succ_cases {d d' : D} {e : Event} (h : succ p L g d e = some (some d')) :
    StepConcl d d' e := by
  obtain ⟨s, v, k⟩ := d
  revert h
  cases s with
  | setmax => exact succOk_setmax v k e d'
  | bar1 => exact succOk_bar1 v k e d'
  | arr a => exact succOk_arr a v k e d'
  | word sk => exact succOk_word sk v k e d'
  | down sk => exact succOk_down sk v k e d'
  | up sk j => exact succOk_up sk j v k e d'
  | total sk => exact succOk_total sk v k e d'
  | vote l => exact succOk_vote l v k e d'
  | pre l => exact succOk_pre l v k e d'
  | tiles l => exact succOk_tiles l v k e d'
  | q0 => exact succOk_q0 v k e d'
  | q1 => exact succOk_q1 v k e d'
  | uk => exact succOk_uk v k e d'
  | nb a => exact succOk_nb a v k e d'
  | free => exact succOk_free v k e d'
  | rbar st => exact succOk_rbar st v k e d'
  | rscale st => exact succOk_rscale st v k e d'
  | rvote st => exact succOk_rvote st v k e d'
  | rld st c => exact succOk_rld st c v k e d'
  | rldw st c => exact succOk_rldw st c v k e d'
  | rst st c => exact succOk_rst st c v k e d'
  | rwait st => exact succOk_rwait st v k e d'
  | rarr st b => exact succOk_rarr st b v k e d'
  | farr0 => exact succOk_farr0 v k e d'
  | fbar st => exact succOk_fbar st v k e d'
  | fsum st => exact succOk_fsum st v k e d'
  | fmax st => exact succOk_fmax st v k e d'
  | farr st => exact succOk_farr st v k e d'
  | fw st b => exact succOk_fw st b v k e d'
  | fld st j => exact succOk_fld st j v k e d'
  | fwl st j => exact succOk_fwl st j v k e d'
  | fst st j b => exact succOk_fst st j b v k e d'
  | fence st => exact succOk_fence st v k e d'
  | fdone st b => exact succOk_fdone st b v k e d'
  | lse a => exact succOk_lse a v k e d'
  | wend l => exact succOk_wend l v k e d'
  | barEnd l => exact succOk_barEnd l v k e d'
  | exit l => exact succOk_exit l v k e d'

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
