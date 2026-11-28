-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Startup.Machine
public import Lemmas.Flow.ParamObject

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Startup
open PTX PTX.Proof PTX.Flow

theorem asms_localRule_mem {L : Launch} {g : Nat} {t : TState} {ma : MemAccess} :
    ∀ a ∈ Assumptions.all, a.localRule L g t (.mem ma) = none := by
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

theorem asms_localRule_bra {L : Launch} {g : Nat} {t : TState} {target : Nat} {uni : Bool} :
    ∀ a ∈ Assumptions.all, a.localRule L g t (.bra target uni) = none := by
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

theorem at_set_live {pc d : Nat} {t : TState} {vreg : Nat → Value} {v : Value}
    (h : At t pc (factsFrom (Flow.live pc) vreg)) (hv : vreg d = v)
    (hl : ∀ r ∈ Flow.live (pc + 1), r = d ∨ r ∈ Flow.live pc) :
    At (PTX.next (setReg t d v)) (pc + 1) (factsFrom (Flow.live (pc + 1)) vreg) := by
  obtain ⟨hpc, hsub, hacc, hf, hregs⟩ := h
  refine ⟨congrArg (· + 1) hpc, hsub, hacc, hf, holds_of_pointwise fun r hr => ?_⟩
  rcases hl r hr with rfl | hr'
  · simp [setReg, PTX.next, hv]
  · by_cases hd : r = d
    · subst hd
      simp [setReg, PTX.next, hv]
    · simp only [setReg, PTX.next, Function.update_of_ne hd]
      exact holds_mem hregs (mem_factsFrom hr')

/-- `ld.param` of a scalar parameter as a segment of one step. -/
theorem seg_ldParam {L : Launch} {g pc d w : Nat} {vreg : Nat → Value} {p : String} {x : BitVec 64}
    {ty : DType}
    (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] }⟩)
    (hw : ty.width = w) (hx : L.params p = some x) (hsf : Assumption.SegFreePc Assumptions.all pc)
    (hv : vreg d = .bits w (truncBits w x))
    (hl : ∀ r ∈ Flow.live (pc + 1), r = d ∨ r ∈ Flow.live pc)
    (hm : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty,
        addr := ⟨.param p false, 0⟩, dsts := [some d] } = some .threadMove := by rfl) :
    Seg kernel Assumptions.all L g 1 pc (factsFrom (Flow.live pc) vreg) (pc + 1)
      (factsFrom (Flow.live (pc + 1)) vreg) := by
  intro t h
  refine ⟨_, run_local hc rfl h
    (exec_ldParam hx (Assumption.SegFreePc.of_eq h.1 hsf) asms_localRule_mem hw hm), ?_⟩
  exact at_set_live h hv hl

end PTX.Kernels.InklingRelDecode.Proof.Startup
