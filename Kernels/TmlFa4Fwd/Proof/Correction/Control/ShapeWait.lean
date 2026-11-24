-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.ShapeScalar
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX PTX.Proof PTX.Flow
noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {p L m g} (hp : Pre p L m) (v : V) (k : Fin 4)
include hp

theorem shape_fw (st a : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.fw st a, v, k⟩ := by
  fin_cases st <;> fin_cases a
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8473)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6496) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 6495) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 144) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_wait (P := Ev p L g _) (q := 0) hf rfl ?_ hl (fun ok => ⟨ok, rfl⟩)

    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8476)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6498) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 6497) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 224) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_wait (P := Ev p L g _) (q := 1) hf rfl ?_ hl (fun ok => ⟨ok, rfl⟩)

    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8769)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6496) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 6499) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 152) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_wait (P := Ev p L g _) (q := 0) hf rfl ?_ hl (fun ok => ⟨ok, rfl⟩)

    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8772)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6498) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 7131) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 232) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_wait (P := Ev p L g _) (q := 1) hf rfl ?_ hl (fun ok => ⟨ok, rfl⟩)

    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl

omit hp in
theorem shape_fence (st : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.fence st, v, k⟩ := by
  fin_cases st
  all_goals ctl_step

omit hp in
theorem shape_rwait (st : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.rwait st, v, k⟩ := by
  fin_cases st
  all_goals ctl_step

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
