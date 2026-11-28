-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Seg
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Local
public import Lemmas.Flow.ParamObject

@[expose] public section

/-! # The local steps no assumption names, and the parameter-pointer steps

Moved from the old tree's `Proof/Thread/Wg1Idle.lean` (by way of the abandoned `flashmla-proof2`
branch): the steps the assumption list leaves to Core (address instructions, and integer
instructions outside the audited parameter-pointer, shared-pointer and peer-score sites) and the
steps of the kernel's parameter-pointer reading (`Assumptions.paramPointers`): the elected lane's
descriptor additions and prefetches. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-! ### Local steps no assumption names, and the parameter-pointer steps -/

/-- The local rules of the assumptions on an address instruction are all empty. -/
theorem localRule_none_addr (t : TState) (ai : AddrInstr) :
    ∀ a ∈ asms, a.localRule L g t (.addr ai) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Assumptions.paramPointers]
  · rfl
  · simp [Assumptions.sharedBits, Assumptions.deadPackRule]
  · rfl

/-- A local step whose rule the assumption list selects is that rule's outcome. -/
theorem run_paramRule {t t' : TState} {pc : Nat} {op : Op} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (h : At t pc F) (hl : op.isLocal = true)
    (hfind : asms.findSome? (fun a => a.localRule L g t op) = some (pure t')) :
    run kernel asms L g 1 t = some t' := by
  refine run_local hc hl h ?_
  rw [execLocalA_noSegment (asms_segment_free L g t)]
  unfold execLocalRule
  rw [hfind]
  rfl

/-- `cvta.param.u64` of the `param_1` object's address: the thread's generic pointer to it. -/
theorem run_cvtaParam {t : TState} {pc d a : Nat} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .addr (.cvta false .param 64 d (.reg a))⟩)
    (h : At t pc F) (hr : t.regs a = some (.ptr 64 false (.param (param "1")) 0)) :
    run kernel asms L g 1 t =
      some (PTX.next (setReg t d (.ptr 64 true (.param (param "1")) 0))) := by
  refine run_local hc rfl h ?_
  rw [execLocalA_noSegment (asms_segment_free L g t),
    execLocalRule_of_none (localRule_none_addr t _)]
  simp only [execLocal_cvta (c := .cvta false .param 64 d (.reg a)) (by rfl), execCvta,
    readValue, readReg, hr, bind, Except.bind, pure, Except.pure]
  simp

/-- A descriptor-offset addition is independent of the vector cursor and accumulator. -/
theorem paramAdd_exec {t : TState} {pc d a : Nat} {k : Int}
    (hpc : t.pc = pc) (hcon : paramAdds.contains pc = true)
    (hr : t.regs a = some (.ptr 64 true (.param (param "1")) 0))
    (hp : L.paramObjects (param "1") = some (mapParam, P.param1Base)) (hk : 0 ≤ k) :
    execLocalA asms L g t (.int ⟨.add, .int .s 64, false, [some d], [.reg a, .imm k]⟩) =
      .ok (PTX.next (setReg t d (.bits 64 (BitVec.ofNat 64 (P.param1Base + k.toNat))))) := by
  rw [execLocalA_noSegment (asms_segment_free L g t)]
  unfold execLocalRule
  simp only [asms, Assumptions.all, List.findSome?_cons, Assumptions.idealArith,
    Assumptions.approx, Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
    Assumptions.lg2Exact, Assumptions.ncReadOnly, Assumption.idealReal, Assumption.approxExact,
    Assumption.ncReadOnly, Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp,
    Assumptions.storeDrain, Assumptions.paramPointers, hpc, hcon, readReg, hr,
    Assumptions.offsetOf, pure, Except.pure]
  repeat' split
  all_goals first | omega | simp_all

/-- A descriptor-offset addition on the `param_1` object's generic address, by the kernel's
parameter-pointer reading: the register receives the numeric address of the descriptor. -/
theorem run_paramAdd {t : TState} {pc d a : Nat} {k : Int} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 64, false, [some d],
      [.reg a, .imm k]⟩⟩)
    (h : At t pc F) (hcon : paramAdds.contains pc = true)
    (hr : t.regs a = some (.ptr 64 true (.param (param "1")) 0))
    (hp : L.paramObjects (param "1") = some (mapParam, P.param1Base)) (hk : 0 ≤ k) :
    run kernel asms L g 1 t =
      some (PTX.next (setReg t d (.bits 64 (BitVec.ofNat 64 (P.param1Base + k.toNat))))) :=
  run_local hc rfl h (paramAdd_exec h.1 hcon hr hp hk)

/-- A descriptor-offset addition whose offset is a register holding a 64-bit word `x`. -/
theorem paramAddReg_exec {t : TState} {pc d a r : Nat} {x : BitVec 64}
    (hpc : t.pc = pc) (hcon : paramAdds.contains pc = true)
    (hr : t.regs a = some (.ptr 64 true (.param (param "1")) 0))
    (hx : t.regs r = some (.bits 64 x))
    (hp : L.paramObjects (param "1") = some (mapParam, P.param1Base)) :
    execLocalA asms L g t (.int ⟨.add, .int .s 64, false, [some d], [.reg a, .reg r]⟩) =
      .ok (PTX.next (setReg t d (.bits 64 (BitVec.ofNat 64 (P.param1Base + x.toNat))))) := by
  rw [execLocalA_noSegment (asms_segment_free L g t)]
  unfold execLocalRule
  simp only [asms, Assumptions.all, List.findSome?_cons, Assumptions.idealArith,
    Assumptions.approx, Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
    Assumptions.lg2Exact, Assumptions.ncReadOnly, Assumption.idealReal, Assumption.approxExact,
    Assumption.ncReadOnly, Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp,
    Assumptions.storeDrain, Assumptions.paramPointers, hpc, hcon, readReg, hr, hx,
    Assumptions.offsetOf, pure, Except.pure]
  repeat' split
  all_goals first | omega | simp_all

/-- `run_paramAdd` with the offset in a register. -/
theorem run_paramAddReg {t : TState} {pc d a r : Nat} {x : BitVec 64} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .int ⟨.add, .int .s 64, false, [some d],
      [.reg a, .reg r]⟩⟩)
    (h : At t pc F) (hcon : paramAdds.contains pc = true)
    (hr : t.regs a = some (.ptr 64 true (.param (param "1")) 0))
    (hx : t.regs r = some (.bits 64 x))
    (hp : L.paramObjects (param "1") = some (mapParam, P.param1Base)) :
    run kernel asms L g 1 t =
      some (PTX.next (setReg t d (.bits 64 (BitVec.ofNat 64 (P.param1Base + x.toNat))))) :=
  run_local hc rfl h (paramAddReg_exec h.1 hcon hr hx hp)

/-- A `prefetch.tensormap` of a published descriptor of the `param_1` object, by the kernel's
parameter-pointer reading: the prefetch has no effect on the thread's state. -/
theorem run_prefetchMap {t : TState} {pc a : Nat} {x : BitVec 64} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .prefetchTensorMap true 64 (.reg a)⟩)
    (h : At t pc F) (hpub : prefetchTensorMapSites.contains pc = true)
    (hdisj : paramAdds.contains pc = false)
    (hr : t.regs a = some (.bits 64 x))
    (hm : (L.tensorMaps x.toNat).isSome = true) :
    run kernel asms L g 1 t = some (PTX.next t) := by
  have hpc : t.pc = pc := h.1
  refine run_paramRule hc h rfl ?_
  simp only [asms, Assumptions.all, List.findSome?_cons, Assumptions.idealArith,
    Assumptions.approx, Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
    Assumptions.lg2Exact, Assumptions.ncReadOnly, Assumption.idealReal, Assumption.approxExact,
    Assumption.ncReadOnly, Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp,
    Assumptions.storeDrain, Assumptions.paramPointers, hpc, hpub, hdisj, readValue, readReg, hr, hm,
    bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals first | omega | simp_all

/-- A register not among a list's keys, after adding one key. -/
theorem not_mem_facts_cons {F : List (Nat × Value)} {r s : Nat} {v : Value}
    (h1 : s ≠ r) (h2 : ∀ p ∈ F, p.1 ≠ r) : ∀ p ∈ (s, v) :: F, p.1 ≠ r := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h1
  · exact h2 p hp

/-- The parameter-pointer reading names no rule outside its descriptor sites. -/
theorem paramPointers_localRule_none {L : Launch} {g : Nat} {t : TState} {op : Op}
    (h1 : t.pc ∉ paramAdds) (h2 : t.pc ∉ prefetchTensorMapSites) :
    Assumptions.paramPointers.localRule L g t op = none := by
  simp [Assumptions.paramPointers, h1, h2]

/-- No assumption of the kernel's list has a local rule for one of the role's integer
instructions. -/
theorem asms_localRule_int {L : Launch} {g : Nat} {t : TState} {i : IntInstr}
    (h1 : t.pc ∉ paramAdds) (h2 : t.pc ∉ prefetchTensorMapSites)
    (h3 : t.pc ∉ Assumptions.sharedBitsSites)
    (hp : Assumptions.peerPackRule t (.int i) = none) :
    ∀ a ∈ asms, a.localRule L g t (.int i) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none (fun f hf => by
      simp [Assumption.FloatForm.ofOp] at hf)
  · exact Assumption.approxExact_localRule_none (fun f hf => by
      simp [Assumption.ApproxForm.ofOp] at hf)
  · simp only [Assumptions.mulBf16x2]
  · simp only [Assumptions.cvtBf16x2]
  · simp only [Assumptions.cvtUe8m0]
  · simp only [Assumptions.lg2Exact]
  · rfl
  · exact paramPointers_localRule_none h1 h2
  · rfl
  · simp [Assumptions.sharedBits, Assumptions.deadPackRule, h3, hp]
  · rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
