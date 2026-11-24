-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Tactics.KernelRfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader

private theorem loaderCoreSlice :
    ((kernel.code.drop 174).take (1906 - 174)).all (fun i => Assumptions.coreOp i.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

/-- The loader dispatch, scheduler and copy pipeline use Core instruction templates. -/
theorem loaderOutCore {l : Launch} {g : Nat} {t : TState}
    (hLo : 174 ≤ t.pc) (hHi : t.pc < 1906) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  have hs : t.pc ∉ Assumptions.swExp2Sites := by
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hl : t.pc ∉ Assumptions.tcLdDataflowSites := by
    simp only [Assumptions.tcLdDataflowSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have ht : t.pc ∉ Assumptions.delayedTmemSites := by
    simp only [Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 174).take (1906 - 174) := by
      apply List.mem_of_getElem? (i := t.pc - 174)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    exact Assumptions.out_all_eq_nil hs hl ht hc (List.all_eq_true.mp loaderCoreSlice ins hm)

end PTX.Kernels.TmlFa4Fwd.Loader
