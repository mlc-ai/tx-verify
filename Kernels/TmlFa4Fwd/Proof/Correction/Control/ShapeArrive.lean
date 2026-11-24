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

theorem shape_rarr (st a : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.rarr st a, v, k⟩ := by
  fin_cases st <;> fin_cases a
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8223)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6236) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 1614) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 96) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8224)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6236) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 1628) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 200) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8442)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6494) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 1615) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 104) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8443)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6494) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 1069) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 192) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl

theorem shape_farr0 :
    (code p L g).ShapeAt (Ev p L g) ⟨.farr0 , v, k⟩ := by
  intro t ins e o hat hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8464)
  have ⟨_, _, _, _, regs⟩ := hat
  have hr := regs_of_factsFrom (r := 6498) regs
    (by dsimp only [live, D.site]; decide +kernel)
  have hb := regs_of_factsFrom (r := 1628) regs
    (by dsimp only [live, D.site]; decide +kernel)
  have hl := Epilogue.loc_off (g := g) (k := 200) (off := 0) hp (by decide) (by decide)
    (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
  refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
  simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
  rfl

theorem shape_farr (st : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.farr st, v, k⟩ := by
  fin_cases st
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8468)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6498) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 1069) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 192) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8764)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6498) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 1628) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 200) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl

theorem shape_fdone (st a : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.fdone st a, v, k⟩ := by
  fin_cases st <;> fin_cases a
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8759)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6498) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 1614) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 96) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_8760)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6498) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 2390) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 208) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_9055)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6498) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 1615) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 104) (off := 0) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl
  · intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_9056)
    have ⟨_, _, _, _, regs⟩ := hat
    have hr := regs_of_factsFrom (r := 6498) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hb := regs_of_factsFrom (r := 2535) regs
      (by dsimp only [live, D.site]; decide +kernel)
    have hl := Epilogue.loc_off (g := g) (k := 0) (off := 216) hp (by decide) (by decide)
      (by have := hp.shared; omega) (hr := hb.trans (by ctl_val))
    refine shape_arrive (P := Ev p L g _) (n := 1) hf rfl rfl ?_ hl rfl
    simp only [readBits, readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
    rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
