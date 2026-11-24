-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.StoreVals
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part126
import Kernels.TmlFa4Fwd.Flow.Code.Part127
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part129
import Kernels.TmlFa4Fwd.Flow.Code.Part130
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Kernels.TmlFa4Fwd.Proof.Correction.SafeTm
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The values of the rescale stores (`rst_val`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option maxHeartbeats 16000000 in
private theorem rst_val0 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState}
    {c : Fin 8} (h : (code p L g).AtD ⟨.rst 0 c, v, k⟩ t)
    (hc : kernel.code[(Site.rst 0 c).pc]? = some ins)
    (hf : Fires (Site.rst 0 c).pc (eventTmpl Assumptions.all L g t ins.op) e o) {a : Nat}
    {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    vals = (List.range 16).map fun i => fv ((sOf v 0).mul (v.xs i)) := by
  have hreg : ∀ r ∈ Flow.live (Site.rst 0 c).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  fin_cases c <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine tcSt_vals (f := fun i => fv ((sOf v _).mul (v.xs i))) (fun s h => by cases h)
      (fun i hi => ?_) hf hk
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> exact ⟨_, rfl, hreg _ (by lit_mem)⟩

set_option maxHeartbeats 16000000 in
private theorem rst_val1 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState}
    {c : Fin 8} (h : (code p L g).AtD ⟨.rst 1 c, v, k⟩ t)
    (hc : kernel.code[(Site.rst 1 c).pc]? = some ins)
    (hf : Fires (Site.rst 1 c).pc (eventTmpl Assumptions.all L g t ins.op) e o) {a : Nat}
    {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    vals = (List.range 16).map fun i => fv ((sOf v 1).mul (v.xs i)) := by
  have hreg : ∀ r ∈ Flow.live (Site.rst 1 c).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  fin_cases c <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    refine tcSt_vals (f := fun i => fv ((sOf v _).mul (v.xs i))) (fun s h => by cases h)
      (fun i hi => ?_) hf hk
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> exact ⟨_, rfl, hreg _ (by lit_mem)⟩

/-- **The values of a rescale store**: the loaded elements times the stage's scale. -/
theorem rst_val {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {st : Fin 2} {c : Fin 8} (h : (code p L g).AtD ⟨.rst st c, v, k⟩ t)
    (hc : kernel.code[(Site.rst st c).pc]? = some ins)
    (hf : Fires (Site.rst st c).pc (eventTmpl Assumptions.all L g t ins.op) e o) {a : Nat}
    {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    vals = (List.range 16).map fun i => fv (v.xs i * (sOf v st).real) := by
  simp only [← Sc.mul_eq]
  fin_cases st
  · exact rst_val0 h hc hf hk
  · exact rst_val1 h hc hf hk

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
