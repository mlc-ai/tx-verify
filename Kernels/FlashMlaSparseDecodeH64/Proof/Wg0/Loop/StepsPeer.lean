-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.Base
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part006
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part007
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part008
import Lemmas.Flow.IssueNext
import Lemmas.Flow.StoreU

@[expose] public section

/-! # Warpgroup 0's obligations at the peer exchange (pcs 403–572)

The eight 16-byte stores of the packed scores to the peer exchange buffer (`pst`; the peer-score
packs of `Assumptions.peerPack`, pcs 394–473, are local rules that `rulesFrame` covers, so the
segments between the stores are havoc segments), named barrier 10/11 (`bar1`), the eight
two-element peer reads (`pld`, element by element), the row-maximum store, barrier and read
(`mst`, `bar2`, `mld`) and the arrival that frees the valid-mask slot (`arrV`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

set_option hygiene false in
local macro "st_at " code:term:max : tactic => `(tactic| (
  refine Code.scalarStoreU $code rfl rfl rfl (fun _ => rfl) rfl rfl rfl rfl Nat.one_pos ?_
  w0_seg))

/-- The eight stores to the peer exchange buffer. -/
theorem stepAt_pst (d : D) (k : Fin 8) (hs : d.site = .pst k) : (code P L g w).StepAtU d := by
  w0_site
  fin_cases k
  · st_at Flow.code_403
  · st_at Flow.code_413
  · st_at Flow.code_423
  · st_at Flow.code_433
  · st_at Flow.code_443
  · st_at Flow.code_453
  · st_at Flow.code_463
  · st_at Flow.code_473

theorem stepAt_bar1 (d : D) (hs : d.site = .bar1) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_475 by exact fires_barSyncN_next hf
  w0_seg

set_option hygiene false in
local macro "rd0 " code:term:max : tactic => `(tactic| (
  exact pld0U rfl rfl (by rfl) $code rfl rfl rfl rfl rfl (by decide +kernel)))

set_option hygiene false in
local macro "rd1 " S:term:max code:term:max : tactic => `(tactic| (
  refine pld1U $S rfl rfl (by rfl) $code rfl rfl rfl rfl rfl rfl (by decide +kernel)
    (Nat.zero_lt_succ _) ?_
  w0_seg))

/-- The first elements of the eight peer reads. -/
theorem stepAt_pld_first (d : D) (k : Fin 8) (hs : d.site = .pld k) (he : d.el = 0) :
    (code P L g w).StepAtU d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  dsimp only at hs he; subst hs he
  fin_cases k
  · rd0 Flow.code_477
  · rd0 Flow.code_482
  · rd0 Flow.code_487
  · rd0 Flow.code_492
  · rd0 Flow.code_497
  · rd0 Flow.code_502
  · rd0 Flow.code_507
  · rd0 Flow.code_512

/-- The second elements of the eight peer reads. -/
theorem stepAt_pld_second (d : D) (k : Fin 8) (hs : d.site = .pld k) (he : d.el = 1) :
    (code P L g w).StepAtU d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  dsimp only at hs he; subst hs he
  fin_cases k
  · rd1 (.pld 1) Flow.code_477
  · rd1 (.pld 2) Flow.code_482
  · rd1 (.pld 3) Flow.code_487
  · rd1 (.pld 4) Flow.code_492
  · rd1 (.pld 5) Flow.code_497
  · rd1 (.pld 6) Flow.code_502
  · rd1 (.pld 7) Flow.code_507
  · rd1 .mst Flow.code_512

/-- The eight two-element peer reads. -/
theorem stepAt_pld (d : D) (k : Fin 8) (hs : d.site = .pld k) : (code P L g w).StepAtU d :=
  el01 (by rw [hs]; rfl) (stepAt_pld_first _ k hs rfl) (stepAt_pld_second _ k hs rfl)

theorem stepAt_mst (d : D) (hs : d.site = .mst) : (code P L g w).StepAtU d := by
  w0_site
  st_at Flow.code_566

theorem stepAt_bar2 (d : D) (hs : d.site = .bar2) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_569 by exact fires_barSyncN_next hf
  w0_seg

/-- The arrival that frees the valid-mask slot (no state register). -/
theorem stepAt_arrV (d : D) (hs : d.site = .arrV) : (code P L g w).StepAtU d := by
  w0_site
  w0_adv Flow.code_571 by exact Code.fires_arrive_next hf
  w0_seg

/-- The partner's row maximum: any payload continues to the vote. -/
theorem stepAt_mld (d : D) (hs : d.site = .mld) : (code P L g w).StepAtU d := by
  w0_site
  refine Code.step_loadU Flow.code_572 rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
    Nat.one_pos (by
      change _ ∉ (factsFrom _ _).map Prod.fst; rw [factsFrom_keys]
      show _ ∉ ctlLive 572; decide +kernel) ?_
  w0_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
