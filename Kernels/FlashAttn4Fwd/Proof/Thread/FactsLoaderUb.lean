-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoader

@[expose] public section

/-! # The loader's sites are not undefined behaviour

At every site of the loader, the instruction's event is not undefined behaviour
(`Loader.tmpl_ok`, the loader's part of `Cross.SitesTmplOk`): every event a site fires has the
site's shape (`Loader.site_event`), and no shape is undefined behaviour. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- **No site of the loader has an undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {ins : Instr}
    (h : At t d.site.pc (facts L g d)) (hi : Inv L g d)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  refine Code.Shape.not_ub (C := code asms L g) (site_event hpre hg) (fun d e f hev hk => ?_) h hi
    hc f
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  cases site <;> (try cases ‹UseK›) <;>
    simp only [Ev, PollIs, ArriveIs, reduceCtorEq, exists_false, false_and] at hev

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

/-- **The loader's part of `Cross.SitesTmplOk`**: at a loader state of the composed machine,
the site's instruction has no undefined-behaviour template. -/
theorem Cross.SitesTmplOk_loader {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {g : Nat} (hg : g < L.threads) (d : Loader.D) (t : TState) (ins : Instr)
    (hat : (code L g).AtD (.inr (.loader d)) t) (hi : (code L g).inv (.inr (.loader d)))
    (hc : kernel.code[(code L g).pc (.inr (.loader d))]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f :=
  Loader.tmpl_ok hpre hg ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩ hi hc f

end PTX.Kernels.FlashAttn4Fwd.Proof
