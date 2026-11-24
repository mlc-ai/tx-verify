-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Lemmas.Flow.LandsU
import Lemmas.Flow.Vector

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof
noncomputable section

private theorem decode (b : Bool) (c : Fin 16) :
    ∃ a, kernel.code[(Site.bld b c).pc]? = some ⟨none, .mem a⟩ ∧
      a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs.length = 4 ∧
      (Op.mem a).isLocal = false := by
  cases b <;> fin_cases c <;> exact ⟨_, by code_lookup, rfl, rfl, rfl, rfl, rfl⟩

/-- Every nonfinal bias word advances the vector load, with arbitrary accumulated values.
Failure to rebuild the returned bytes reaches a concrete UB at this substep. -/
theorem stepAt_bld_midU {p L g} (b : Bool) (c : Fin 16) (v : V) (k : Fin 4)
    (acc : List Value) (hk : k.val < 3) : (code p L g).StepAtU ⟨.bld b c,v,k,acc⟩ := by
  obtain ⟨a,hc,hl,hn,hx,h4,hnl⟩ := decode b c
  refine ⟨fun _ => ⟨_,hc,hnl,trivial⟩, ?_⟩
  intro t e u ins hat hi hdec hf
  obtain rfl := Option.some.inj (hdec.symm.trans hc)
  obtain ⟨addr,bs,rfl,rfl⟩ := fires_load hl hn hf hx
  obtain ⟨hpc,hsub,hacc,hfault,hr⟩ := hat
  change acc.length = k.val at hi
  change t.sub = k.val at hsub
  let d' : D := ⟨.bld b c,v,k+1,acc ++ [(rebuild 3 bs).toOption.getD (.bits 32 0)]⟩
  have hnext : succ p L g ⟨.bld b c,v,k,acc⟩ ⟨(Site.bld b c).pc,.rd addr bs⟩ = some (some d') := by
    simp only [succ,hk,↓reduceIte,d']
  suffices h : ∃ s, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
      (afterLoad t a.regs bs) s ∧ (code p L g).GoodU (some d') s by
    obtain ⟨s,h⟩ := h
    exact .inl (.inr ⟨d',s,hnext,h⟩)
  cases hv : rebuild 3 bs with
  | error f =>
    exact Code.goodU_of_dead (C := code p L g) d' (Machine.dead_of_fault (afterLoad_fault hv))
  | ok w =>
    have hvk : (k+1 : Fin 4).val = k.val + 1 := by omega
    rw [afterLoad_mid hv (by omega)]
    refine ⟨_, .refl, .inl ⟨⟨hpc, hsub ▸ hvk.symm, ?_, hfault, hr⟩, ?_⟩⟩
    · simp only [d',hacc,hv]; rfl
    · change (acc ++ [_]).length = (k+1 : Fin 4).val
      simp only [List.length_append,List.length_singleton,hi,hvk]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
