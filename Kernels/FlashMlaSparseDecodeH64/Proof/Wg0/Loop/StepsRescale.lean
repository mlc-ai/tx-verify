-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.Base
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part011
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part012
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part013
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part014
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part015
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part016
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part017
import Lemmas.Flow.TensorStoreU
import Lemmas.Flow.RoleTemplates

@[expose] public section

/-! # Warpgroup 0's obligations at the rescale arm and the proxy fence (pcs 711–1120)

The fence opening the arm (`rsf`), per 64-column chunk `c` the accumulator load, its wait, the
rescaled store and its wait (`rld c`, `rldw c`, `rst c`, `rstw c`), the closing fence (`rsfb`)
and the proxy fence before the softmax-ready arrival (`fpx`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem stepAt_rsf (d : D) (hs : d.site = .rsf) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_711 by exact Code.fires_tcPlain_next (.inl rfl) hf
  w0_seg

set_option hygiene false in
local macro "ld_at " pc:term:max code:term:max : tactic => `(tactic| (
  refine Code.tcLoadU (live := ctlLive $pc) $code (fun _ h => by cases h) (noLdWait _) rfl
    (by decide +kernel) (fun _ _ => rfl) rfl rfl rfl rfl Nat.one_pos ?_
  w0_seg))

theorem stepAt_rld (d : D) (c : Fin 4) (hs : d.site = .rld c) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases c
  · ld_at 716 Flow.code_716
  · ld_at 817 Flow.code_817
  · ld_at 918 Flow.code_918
  · ld_at 1019 Flow.code_1019

set_option hygiene false in
local macro "wait_ld " code:term:max : tactic => `(tactic| (
  w0_adv $code by exact Code.fires_tcPlain_next (.inr (.inr rfl)) hf
  w0_seg))

theorem stepAt_rldw (d : D) (c : Fin 4) (hs : d.site = .rldw c) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases c
  · wait_ld Flow.code_717
  · wait_ld Flow.code_818
  · wait_ld Flow.code_919
  · wait_ld Flow.code_1020

set_option hygiene false in
local macro "st_tc " code:term:max : tactic => `(tactic| (
  refine Code.tensorStoreU false $code rfl rfl rfl (fun _ => rfl) rfl rfl Nat.one_pos ?_
  w0_seg))

theorem stepAt_rst (d : D) (c : Fin 4) (hs : d.site = .rst c) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases c
  · st_tc Flow.code_814
  · st_tc Flow.code_915
  · st_tc Flow.code_1016
  · st_tc Flow.code_1117

set_option hygiene false in
local macro "wait_st " code:term:max : tactic => `(tactic| (
  w0_adv $code by exact fires_tcWaitSt_next hf
  w0_seg))

theorem stepAt_rstw (d : D) (c : Fin 4) (hs : d.site = .rstw c) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases c
  · wait_st Flow.code_815
  · wait_st Flow.code_916
  · wait_st Flow.code_1017
  · wait_st Flow.code_1118

theorem stepAt_rsfb (d : D) (hs : d.site = .rsfb) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_1119 by exact Code.fires_tcPlain_next (.inr (.inl rfl)) hf
  w0_seg

theorem stepAt_fpx (d : D) (hs : d.site = .fpx) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_1120 by exact Option.some.inj (fires_fence_proxy hf).2
  w0_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
