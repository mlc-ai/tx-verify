-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue

/-- The scheduler and writeback region and the warp's three instructions at the common exit. -/
def EpiloguePc (pc : Nat) : Prop :=
  (2768 ≤ pc ∧ pc ≤ 3100) ∨ (7742 ≤ pc ∧ pc ≤ 7744) ∨ pc = 9205

private theorem slice_coreOps :
    ((kernel.code.drop 2768).take 333).all (fun i => Assumptions.coreOp i.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem slice_coreOp {pc : Nat} {ins : Instr} (hlo : 2768 ≤ pc) (hhi : pc ≤ 3100)
    (hc : kernel.code[pc]? = some ins) : Assumptions.coreOp ins.op = true := by
  have hi : ((kernel.code.drop 2768).take 333)[pc - 2768]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
    exact hc
  exact List.all_eq_true.mp slice_coreOps ins (List.mem_of_getElem? hi)

theorem epilogue_coreOpShared {pc : Nat} {ins : Instr}
    (hp : EpiloguePc pc) (hc : kernel.code[pc]? = some ins) : Assumptions.coreOp ins.op = true := by
  rcases hp with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | h
  · exact slice_coreOp hlo hhi hc
  · have hr : pc = 7742 ∨ pc = 7743 ∨ pc = 7744 := by omega
    rcases hr with rfl | rfl | rfl
    · rw [Flow.code_7742] at hc
      cases hc
      rfl
    · rw [Flow.code_7743] at hc
      cases hc
      rfl
    · rw [Flow.code_7744] at hc
      cases hc
      rfl
  · subst pc
    rw [Flow.code_9205] at hc
    cases hc
    rfl

theorem epilogue_off_exp2Shared {pc : Nat} (hp : EpiloguePc pc) :
    pc ∉ Assumptions.swExp2Sites := by
  unfold EpiloguePc at hp
  simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Synchronization assumptions leave the output warp's event templates and local steps intact. -/
theorem epilogue_out_all_eq_nil {l : Launch} {g : Nat} {t : TState} (hp : EpiloguePc t.pc) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  have hload : t.pc ∉ Assumptions.tcLdDataflowSites := by
    unfold EpiloguePc at hp
    simp only [Assumptions.tcLdDataflowSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hstore : t.pc ∉ Assumptions.delayedTmemSites := by
    unfold EpiloguePc at hp
    simp only [Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    exact Assumptions.out_all_eq_nil (epilogue_off_exp2Shared hp) hload hstore hc
      (epilogue_coreOpShared hp hc)

end PTX.Kernels.TmlFa4Fwd.Epilogue
