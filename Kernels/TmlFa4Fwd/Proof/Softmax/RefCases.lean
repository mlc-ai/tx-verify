-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.Softmax.Ref
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefSucc
import Kernels.TmlFa4Fwd.Proof.Softmax.RefSuccLoad
import Kernels.TmlFa4Fwd.Proof.Softmax.RefSuccP
import Kernels.TmlFa4Fwd.Proof.Softmax.RefSuccScan
import Kernels.TmlFa4Fwd.Proof.Softmax.RefSuccStart

@[expose] public section

/-! # The successors of the softmax machine's states

`succ_cases`: every step of the softmax machine stays at its site with its values and fires no
event of a ledger class, or moves to a listed successor of its site with the step facts
(`MoveFacts`). One theorem per family of sites (`RefSucc*.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {g : Nat}

/-- **Every step of the softmax machine** stays at its site, or moves to a listed successor with
the step facts. -/
theorem succ_cases {d d' : D} {e : Event} (h : succ p L g d e = some (some d')) :
    StepConcl L g d d' e := by
  obtain ⟨s, v, k, acc⟩ := d
  revert h
  cases s with
  | setmax => exact succOk_setmax v k acc e d'
  | bar1 => exact succOk_bar1 v k acc e d'
  | word sk => exact succOk_word sk v k acc e d'
  | down sk => exact succOk_down sk v k acc e d'
  | up sk j => exact succOk_up sk j v k acc e d'
  | total sk => exact succOk_total sk v k acc e d'
  | vote l => exact succOk_vote l v k acc e d'
  | pre l => exact succOk_pre l v k acc e d'
  | tiles l => exact succOk_tiles l v k acc e d'
  | q0 => exact succOk_q0 v k acc e d'
  | q1 => exact succOk_q1 v k acc e d'
  | uk => exact succOk_uk v k acc e d'
  | wq => exact succOk_wq v k acc e d'
  | ws r => exact succOk_ws r v k acc e d'
  | sld r c => exact succOk_sld r c v k acc e d'
  | sldw c => exact succOk_sldw c v k acc e d'
  | wb b => exact succOk_wb b v k acc e d'
  | bld b c => exact succOk_bld b c v k acc e d'
  | fence b => exact succOk_fence b v k acc e d'
  | bsync b => exact succOk_bsync b v k acc e d'
  | barr b => exact succOk_barr b v k acc e d'
  | stat b => exact succOk_stat b v k acc e d'
  | narr r => exact succOk_narr r v k acc e d'
  | pst r q => exact succOk_pst r q v k acc e d'
  | pwst r j => exact succOk_pwst r j v k acc e d'
  | parr r => exact succOk_parr r v k acc e d'
  | pws r => exact succOk_pws r v k acc e d'
  | pel r => exact succOk_pel r v k acc e d'
  | parr2 r => exact succOk_parr2 r v k acc e d'
  | pwend r => exact succOk_pwend r v k acc e d'
  | fin j => exact succOk_fin j v k acc e d'
  | finarr => exact succOk_finarr v k acc e d'
  | wend l => exact succOk_wend l v k acc e d'
  | barEnd l => exact succOk_barEnd l v k acc e d'
  | exit l => exact succOk_exit l v k acc e d'

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
