-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Assumptions
public import Lemmas.Assumption.Facts
public import Lemmas.Flow.RoundTrip

@[expose] public section

/-! # What the kernel's assumptions decide

The ideal-arithmetic assumption decides the epilogue's `cvt.rn.f16x2.f32` (`prod_ideal_cvt`);
the cluster-scope assumption widens exactly the sites of `clusterMbarSites`
(`prod_scope_eq`), which are all mbarrier arrivals and waits of the kernel (`prod_scope_at`);
neither allows non-coherent loads (`prod_noNc`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX

/-- The kernel's assumption list as `Theorem.lean` states it; active in every module that imports
this one and works in the `Proof` namespace. -/
scoped notation "Prod" => [Assumptions.idealArith, Assumptions.clusterMbar, Assumptions.pollAgree]

/-- An mbarrier wait or arrival, the operations whose sites `clusterMbar` names. -/
def mbarSync : Op → Bool
  | .mbarWait .. | .mbarArrive .. => true
  | _ => false

/-- The assumptions widen exactly the sites of `clusterMbarSites`. -/
theorem prod_scope_eq (pc : Nat) :
    List.any Prod (·.clusterScopeMbar pc) = Assumptions.clusterMbarSites.contains pc := by
  simp [Assumptions.idealArith, Assumptions.clusterMbar, Assumption.clusterScopeMbarAt,
    Assumptions.pollAgree, Assumption.pollAgreeAt]

/-- Every mbarrier wait or arrival of the kernel is widened. -/
theorem prod_scope_at {pc : Nat} {ins : Instr} (hc : kernel.code[pc]? = some ins)
    (hs : mbarSync ins.op = true) : List.any Prod (·.clusterScopeMbar pc) = true := by
  rw [prod_scope_eq, Assumptions.clusterMbarSites_eq, List.contains_iff_mem, List.mem_filter,
    List.mem_range]
  refine ⟨(List.getElem?_eq_some_iff.mp hc).1, ?_⟩
  rw [hc, Option.map_some]
  revert hs
  generalize ins.op = op
  cases op <;> simp [mbarSync]

/-- No assumption allows a non-coherent load. -/
theorem prod_noNc (pc : Nat) : List.any Prod (·.ncLoads pc) = false := by
  simp [Assumptions.idealArith, Assumptions.clusterMbar, Assumption.clusterScopeMbarAt,
    Assumptions.pollAgree, Assumption.pollAgreeAt]

/-- The epilogue's conversions are ideal. -/
theorem prod_ideal_cvt : Assumption.IdealFor Prod .cvtRnF16x2F32 :=
  Assumption.idealFor_head (by decide)

/-- An epilogue conversion with a NaN operand, which the ideal rule declines, takes the Core
rule. -/
theorem prod_decline_cvt : Assumption.DeclineCore Prod .cvtRnF16x2F32 :=
  Assumption.declineCore_head fun a ha _ _ _ _ _ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl

/-- No assumption has a local rule for an operation with no floating form: the core rule
applies. -/
theorem prod_localRule_none {op : Op} (h : Assumption.FloatForm.ofOp op = none) (L : Launch)
    (g : Nat) (t : TState) : ∀ a ∈ Prod, a.localRule L g t op = none := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none fun f hf => by rw [h] at hf; cases hf
  · rfl
  · rfl

/-- No assumption has a local rule for a branch: the core rule applies. -/
theorem prod_localRule_bra (L : Launch) (g : Nat) (t : TState) (target : Nat) (uni : Bool) :
    ∀ a ∈ Prod, a.localRule L g t (.bra target uni) = none :=
  prod_localRule_none (by simp [Assumption.FloatForm.ofOp]) L g t

/-- No assumption names the 128-bit unpack of a register into two halves. -/
theorem prod_noUnpack128 : Flow.NoUnpack128 Prod := fun lo hi src L g t =>
  prod_localRule_none (op := .move ⟨.unpack, .int .b 128, [some lo, some hi], [.reg src]⟩)
    (by simp [Assumption.FloatForm.ofOp]) L g t

/-- No assumption names the 128-bit pack of two halves into one register. -/
theorem prod_noPack128 : Flow.NoPack128 Prod := fun d lo hi L g t =>
  prod_localRule_none (op := .move ⟨.pack, .int .b 128, [some d], [.reg lo, .reg hi]⟩)
    (by simp [Assumption.FloatForm.ofOp]) L g t

end PTX.Kernels.Fp16Gemm8192.Proof
