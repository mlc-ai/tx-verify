-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictLib
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part012
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part013
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part014
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part015
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part016
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part017
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018
import Lemmas.Flow.IssueNext
import Lemmas.Flow.CtlStepsU

@[expose] public section

/-! # Warpgroup 0's strict steps at the rescale stores -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem stepAt_rst0S (d : D) (hs : d.site = .rst 0) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine stepAt_tcStS (pc := 814) (dn := ⟨.rstw 0, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
    rfl Flow.code_814 (by decide +kernel) (fun _ => rfl) rfl rfl Nat.one_pos ?_
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

theorem stepAt_rstw0S (d : D) (hs : d.site = .rstw 0) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_815, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨.rld 1, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
      Flow.code_815 (fun hf => fires_tcWaitSt_next hf) (fun _ => rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

theorem stepAt_rst1S (d : D) (hs : d.site = .rst 1) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine stepAt_tcStS (pc := 915) (dn := ⟨.rstw 1, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
    rfl Flow.code_915 (by decide +kernel) (fun _ => rfl) rfl rfl Nat.one_pos ?_
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

theorem stepAt_rstw1S (d : D) (hs : d.site = .rstw 1) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_916, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨.rld 2, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
      Flow.code_916 (fun hf => fires_tcWaitSt_next hf) (fun _ => rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

theorem stepAt_rst2S (d : D) (hs : d.site = .rst 2) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine stepAt_tcStS (pc := 1016) (dn := ⟨.rstw 2, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
    rfl Flow.code_1016 (by decide +kernel) (fun _ => rfl) rfl rfl Nat.one_pos ?_
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

theorem stepAt_rstw2S (d : D) (hs : d.site = .rstw 2) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_1017, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨.rld 3, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
      Flow.code_1017 (fun hf => fires_tcWaitSt_next hf) (fun _ => rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

theorem stepAt_rst3S (d : D) (hs : d.site = .rst 3) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine stepAt_tcStS (pc := 1117) (dn := ⟨.rstw 3, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
    rfl Flow.code_1117 (by decide +kernel) (fun _ => rfl) rfl rfl Nat.one_pos ?_
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

theorem stepAt_rstw3S (d : D) (hs : d.site = .rstw 3) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_1118, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨.rsfb, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
      Flow.code_1118 (fun hf => fires_tcWaitSt_next hf) (fun _ => rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

theorem stepAt_rstS (c : Fin 4) (d : D) (hs : d.site = .rst c) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  fin_cases c
  · exact stepAt_rst0S d hs he
  · exact stepAt_rst1S d hs he
  · exact stepAt_rst2S d hs he
  · exact stepAt_rst3S d hs he

theorem stepAt_rstwS (c : Fin 4) (d : D) (hs : d.site = .rstw c) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  fin_cases c
  · exact stepAt_rstw0S d hs he
  · exact stepAt_rstw1S d hs he
  · exact stepAt_rstw2S d hs he
  · exact stepAt_rstw3S d hs he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
