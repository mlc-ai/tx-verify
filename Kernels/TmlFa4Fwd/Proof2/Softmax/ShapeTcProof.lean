-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Shape

@[expose] public section

/-! # Shape proofs for Tensor Memory instructions at sub-step zero -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- A Tensor Memory address register's value at a state. -/
macro "tm_reg" : tactic => `(tactic|
  exact (PTX.Flow.regs_of_factsFrom hat.2.2.2.2 (by lit_mem)).trans
    (by simp only [valueOf, values, valuesStart, valuesRole, valuesTile, valuesP1, valuesBias,
          valuesPlain, valuesFin, lookupLit, Option.getD_some, Option.getD_none] <;> rfl))

set_option hygiene false in
/-- The Tensor Memory sites at sub-step 0, by hand: the score loads (with their implicit wait
in a plain round), the P stores (the first one of the first and biased rounds waits). -/
macro "soft_tc" : tactic => `(tactic| (
  intro t ins e o hat hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  first
  | (exfalso; simp [Site.first, Site.midOk] at hi; done)
  | (refine PTX.Flow.shape_tcLd hf (by intro s hs; cases hs)
      (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcLdWait]; kernel_rfl)
      (fun a vals => ?_) (fun f => ?_)
     · exact Or.inl ⟨a, vals, _, rfl⟩
     · exact Or.inr ⟨f, rfl⟩)
  | (refine PTX.Flow.shape_tcLdLoad hf (by intro s hs; cases hs)
      (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcLdWait]; kernel_rfl)
      (hat.2.1.trans rfl) (by tm_reg)
      (by first | with_reducible exact or32_lt _ _ | with_reducible exact ori_lt _ _)
      (fun a vals => ?_) (fun f => ?_)
     · exact Or.inl ⟨a, vals, _, rfl⟩
     · exact Or.inr ⟨f, rfl⟩)
  | (refine PTX.Flow.shape_tcStWait hf
      (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl)
      (hat.2.1.trans rfl) (by rw [‹Pre _ _ _›.block]) ?_
     rfl)
  | (refine PTX.Flow.shape_tcSt hf (by tm_reg)
      (by first | with_reducible exact or32_lt _ _ | with_reducible exact ori_lt _ _)
      (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl)
      (fun a vals => ?_) (fun f => ?_)
     · exact Or.inl ⟨a, vals, _, rfl⟩
     · exact Or.inr ⟨f, rfl⟩)))

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
