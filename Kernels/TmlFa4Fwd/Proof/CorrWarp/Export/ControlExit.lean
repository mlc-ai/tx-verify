-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.CorrWarp.NoUb

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX.Flow Correction
variable {p : Params} {L : Launch} {m : Mem0} {g ns nv : Nat} {e : Event}

theorem control_exit (hp : Pre p L m) (hg : g < L.threads) {d : Control.D}
    (hF : CFits p L g d.scheduler ns nv) (hE : CExpect p L g d.scheduler ns e)
    (hD : Control.Expect d e) (hev : Control.Ev p L g d e) (hu : ∀ f, e.kind ≠ .ub f)
    (hn : Control.succ p L g d e = none) : e.kind = .exit := by
  have direct (h : Control.succ p L g d e =
      (Correction.succ p L g d.scheduler e).map (Option.map Control.erase))
      (hdata : ExpectD d.scheduler e) (hshape : Correction.Ev p L g d.scheduler e) :
      e.kind = .exit :=
    next_none hp hg hF hE hdata hshape hu (Option.map_eq_none_iff.mp (h ▸ hn))
  obtain ⟨s,v,k⟩ := d
  cases s with
  | rscale st | fsum st | fmax st =>
    rcases hev with ⟨a,bs,h⟩ | ⟨f,h⟩
    · simp only [Control.succ,h,reduceCtorEq] at hn
    · exact (hu f h).elim
  | rld st c | fld st c =>
    rcases hev with ⟨a,vs,sh,h⟩ | ⟨f,h⟩
    · simp only [Control.succ,h,reduceCtorEq] at hn
    · exact (hu f h).elim
  | rvote st =>
    obtain ⟨pred,b,h⟩ := hev
    simp only [Control.succ,Control.D.scheduler,Correction.succ,h,
      Option.map_some,reduceCtorEq] at hn
  | fdone st i =>
    fin_cases st <;> fin_cases i <;> first | exact direct rfl True.intro hev | cases hn
  | lse i => fin_cases i <;> first | exact direct rfl True.intro hev | cases hn
  | _ => exact direct rfl hD hev

end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
