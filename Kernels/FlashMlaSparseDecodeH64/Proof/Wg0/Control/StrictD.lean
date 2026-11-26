-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictLib
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part007
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part008
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part011
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part012
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part020
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part021
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part023
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part024
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part025
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part026
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part028
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part029
import Lemmas.Flow.IssueNext
import Lemmas.Flow.CtlStepsU

@[expose] public section

/-! # Warpgroup 0's strict steps at the vector stores -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

set_option hygiene false in
/-- A vector-store site's strict step: `stepAt_stS` at `pc`, next site `s`. -/
local macro "stS_site " n:ident " : " site:term " => " pc:num s:term:max c:ident : command =>
  `(theorem $n (d : D) (hs : d.site = $site) : (code P L g w).StepAt d := by
      w0s_state d
      simp only at hs
      subst hs
      refine stepAt_stS (pc := $pc) (s := $s) rfl $c rfl rfl rfl rfl
        (fun k h => by cases h) trivial (by decide) (fun e => rfl) ?_
      dsimp only [code, facts, Site.pc]
      seg_sym using w0_segS)

stS_site stepAt_ostK0S : .ost 0 => 704 (.ost 1) Flow.code_704
stS_site stepAt_ostK1S : .ost 1 => 705 (.ost 2) Flow.code_705
stS_site stepAt_ostK2S : .ost 2 => 706 (.ost 3) Flow.code_706
stS_site stepAt_ost2_0_0S : .ost2 0 0 => 1331 (.ost2 0 1) Flow.code_1331
stS_site stepAt_ost2_0_1S : .ost2 0 1 => 1332 (.ost2 0 2) Flow.code_1332
stS_site stepAt_ost2_0_2S : .ost2 0 2 => 1333 (.ost2 0 3) Flow.code_1333
stS_site stepAt_ost2_0_3S : .ost2 0 3 => 1334 (.ost2 0 4) Flow.code_1334
stS_site stepAt_ost2_0_4S : .ost2 0 4 => 1335 (.ost2 0 5) Flow.code_1335
stS_site stepAt_ost2_0_5S : .ost2 0 5 => 1336 (.ost2 0 6) Flow.code_1336
stS_site stepAt_ost2_0_6S : .ost2 0 6 => 1337 (.ost2 0 7) Flow.code_1337
stS_site stepAt_ost2_0_7S : .ost2 0 7 => 1338 (.ofpx 0) Flow.code_1338
stS_site stepAt_ost2_1_0S : .ost2 1 0 => 1491 (.ost2 1 1) Flow.code_1491
stS_site stepAt_ost2_1_1S : .ost2 1 1 => 1492 (.ost2 1 2) Flow.code_1492
stS_site stepAt_ost2_1_2S : .ost2 1 2 => 1493 (.ost2 1 3) Flow.code_1493
stS_site stepAt_ost2_1_3S : .ost2 1 3 => 1494 (.ost2 1 4) Flow.code_1494
stS_site stepAt_ost2_1_4S : .ost2 1 4 => 1495 (.ost2 1 5) Flow.code_1495
stS_site stepAt_ost2_1_5S : .ost2 1 5 => 1496 (.ost2 1 6) Flow.code_1496
stS_site stepAt_ost2_1_6S : .ost2 1 6 => 1497 (.ost2 1 7) Flow.code_1497
stS_site stepAt_ost2_1_7S : .ost2 1 7 => 1498 (.ofpx 1) Flow.code_1498
stS_site stepAt_ost2_2_0S : .ost2 2 0 => 1649 (.ost2 2 1) Flow.code_1649
stS_site stepAt_ost2_2_1S : .ost2 2 1 => 1650 (.ost2 2 2) Flow.code_1650
stS_site stepAt_ost2_2_2S : .ost2 2 2 => 1651 (.ost2 2 3) Flow.code_1651
stS_site stepAt_ost2_2_3S : .ost2 2 3 => 1652 (.ost2 2 4) Flow.code_1652
stS_site stepAt_ost2_2_4S : .ost2 2 4 => 1653 (.ost2 2 5) Flow.code_1653
stS_site stepAt_ost2_2_5S : .ost2 2 5 => 1654 (.ost2 2 6) Flow.code_1654
stS_site stepAt_ost2_2_6S : .ost2 2 6 => 1655 (.ost2 2 7) Flow.code_1655
stS_site stepAt_ost2_2_7S : .ost2 2 7 => 1656 (.ofpx 2) Flow.code_1656
stS_site stepAt_ost2_3_0S : .ost2 3 0 => 1806 (.ost2 3 1) Flow.code_1806
stS_site stepAt_ost2_3_1S : .ost2 3 1 => 1807 (.ost2 3 2) Flow.code_1807
stS_site stepAt_ost2_3_2S : .ost2 3 2 => 1808 (.ost2 3 3) Flow.code_1808
stS_site stepAt_ost2_3_3S : .ost2 3 3 => 1809 (.ost2 3 4) Flow.code_1809
stS_site stepAt_ost2_3_4S : .ost2 3 4 => 1810 (.ost2 3 5) Flow.code_1810
stS_site stepAt_ost2_3_5S : .ost2 3 5 => 1811 (.ost2 3 6) Flow.code_1811
stS_site stepAt_ost2_3_6S : .ost2 3 6 => 1812 (.ost2 3 7) Flow.code_1812
stS_site stepAt_ost2_3_7S : .ost2 3 7 => 1813 (.ofpx 3) Flow.code_1813

theorem stepAt_ost2S (c : Fin 4) (k : Fin 8) (d : D) (hs : d.site = .ost2 c k) :
    (code P L g w).StepAt d := by
  fin_cases c <;> fin_cases k
  · exact stepAt_ost2_0_0S d hs
  · exact stepAt_ost2_0_1S d hs
  · exact stepAt_ost2_0_2S d hs
  · exact stepAt_ost2_0_3S d hs
  · exact stepAt_ost2_0_4S d hs
  · exact stepAt_ost2_0_5S d hs
  · exact stepAt_ost2_0_6S d hs
  · exact stepAt_ost2_0_7S d hs
  · exact stepAt_ost2_1_0S d hs
  · exact stepAt_ost2_1_1S d hs
  · exact stepAt_ost2_1_2S d hs
  · exact stepAt_ost2_1_3S d hs
  · exact stepAt_ost2_1_4S d hs
  · exact stepAt_ost2_1_5S d hs
  · exact stepAt_ost2_1_6S d hs
  · exact stepAt_ost2_1_7S d hs
  · exact stepAt_ost2_2_0S d hs
  · exact stepAt_ost2_2_1S d hs
  · exact stepAt_ost2_2_2S d hs
  · exact stepAt_ost2_2_3S d hs
  · exact stepAt_ost2_2_4S d hs
  · exact stepAt_ost2_2_5S d hs
  · exact stepAt_ost2_2_6S d hs
  · exact stepAt_ost2_2_7S d hs
  · exact stepAt_ost2_3_0S d hs
  · exact stepAt_ost2_3_1S d hs
  · exact stepAt_ost2_3_2S d hs
  · exact stepAt_ost2_3_3S d hs
  · exact stepAt_ost2_3_4S d hs
  · exact stepAt_ost2_3_5S d hs
  · exact stepAt_ost2_3_6S d hs
  · exact stepAt_ost2_3_7S d hs

theorem stepAt_ostK3S (d : D) (hs : d.site = .ost 3) : (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs
  subst hs
  cases hb : (scmpi .eq .b bi 1 || !vt)
  · refine stepAt_stS (pc := 707) (s := .rsf) rfl Flow.code_707 rfl rfl rfl rfl
      (fun k h => by cases h) trivial (by decide) (fun e => ?_) ?_
    · show some (some (elemNext _ 4 (afterOst _))) = _
      simp only [afterOst, hb]; rfl
    · dsimp only [code, facts, Site.pc]
      seg_sym using w0_segS
  · refine stepAt_stS (pc := 707) (s := .fpx) rfl Flow.code_707 rfl rfl rfl rfl
      (fun k h => by cases h) trivial (by decide) (fun e => ?_) ?_
    · show some (some (elemNext _ 4 (afterOst _))) = _
      simp only [afterOst, hb]; rfl
    · dsimp only [code, facts, Site.pc]
      seg_sym using w0_segS

theorem stepAt_ostS (k : Fin 4) (d : D) (hs : d.site = .ost k) : (code P L g w).StepAt d := by
  fin_cases k
  · exact stepAt_ostK0S d hs
  · exact stepAt_ostK1S d hs
  · exact stepAt_ostK2S d hs
  · exact stepAt_ostK3S d hs

theorem stepAt_pst7S (d : D) (hs : d.site = .pst 7) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine stepAt_stS (pc := 473) (s := .bar1) rfl Flow.code_473 rfl rfl rfl rfl
    (fun k h => by cases h) trivial (by decide) (fun e => rfl) ?_
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
