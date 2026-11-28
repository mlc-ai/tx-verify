-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Entry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
public import Lemmas.Isa.Rule
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamLoad

@[expose] public section

/-! # A scalar `ld.param` through the parameter pointer, as one step

The roles read their scalar parameters with `ld.param.b32` or `ld.param.b64` from `[%rd2+off]`,
where `%rd2` (register 2991) holds the parameter pointer of `param_0`. Evaluating such a load
under the launch with `param_0`'s bytes explicit (`p0_eq`) costs a segment tactic more than a
declaration's budget; `seg_ldp` states the step once: the field `(off, x, n)` of `p0fields` loads
as `.bits (8 n) (BitVec.ofNat 64 (leNat x 0 n))`, the term `pw x` (`n = 4`) or `pw8 x`
(`n = 8`). A walk composes it with the evaluated segments around it (`Seg.comp_ex`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The bytes of a field of `p0fields` read as the field's value, from any byte of it. -/
theorem p0_bitsFrom (hp : Pre P L m) {off x n : Nat} (hf : (off, x, n) ∈ p0fields P L) :
    ∀ j k, k + j ≤ n → paramObjectBits L (param "0") (off + k) j = .ok (leNat x k j)
  | 0, _, _ => rfl
  | j + 1, k, hk => by
    have hb := p0fields_ok hp _ hf k (by simp only; omega)
    have hr := p0_bitsFrom hp hf j (k + 1) (by omega)
    simp only at hb
    rw [show off + (k + 1) = off + k + 1 by omega] at hr
    simp only [paramObjectBits, hb, hr, leNat, bind, Except.bind, pure, Except.pure]

/-- The shape of a scalar `ld.param` of `param_0` through register 2991. -/
abbrev ldpIns (ty : DType) (off : Int) (d : Nat) : Instr :=
  { guard := none,
    op := Op.mem
      { kind := MemKind.load, space := some StateSpace.param, sem := Sem.weak, scope := none,
        elem := ty, vec := 1, ext := MemExt.same, nc := false, noftz := false,
        hints := { cop := none, l1 := none, l2 := none, prefetch := none, policy := none },
        addr := { base := AddrBase.reg 2991 64, off := off }, dsts := [some d], srcs := [],
        mmio := false } }

/-- **A scalar `ld.param` of a field of `param_0`, as one step**: from facts holding the
parameter pointer and not register `d`, the thread steps to the next pc with `d` holding the
field's value. -/
theorem seg_ldp (hp : Pre P L m) {pc d off x n : Nat} {ty : DType} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some (ldpIns ty off d))
    (hty : (ty = .int .b 32 ∧ n = 4) ∨ (ty = .int .b 64 ∧ n = 8)) (hal : off % n = 0)
    (hoff : off + n ≤ 304)
    (hf : (off, x, n) ∈ p0fields P L)
    (h2991 : (2991, .ptr 64 false (.param (param "0")) 0) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d) :
    Seg kernel Assumptions.all L g 1 pc F (pc + 1)
      ((d, .bits (8 * n) (BitVec.ofNat 64 (leNat x 0 n))) :: F) := by
  intro t h
  have hr0 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) :=
    holds_mem (atHolds h) h2991
  have hbits := p0_bitsFrom hp hf n 0 (by omega)
  simp only [Nat.add_zero] at hbits
  refine ⟨_, run_local hc rfl h ?_, At.set h hd⟩
  rw [execLocalA_noSegment (asms_segment_free L g t)]
  rw [execLocalRule_of_none (fun a ha => ?_)]
  · rcases hty with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [execLocal_mem rfl]
      simp [execMove, MemAccess.regs, paramObjectOf, readReg, hr0, hp.param0Object, scalarsParam,
        loadParamObject, hbits, bind, Except.bind, pure, Except.pure, hal, paramElem,
        Functor.map, Except.map, hoff, DType.width, ParamObjectDecl.bytes]
    · rw [execLocal_mem rfl]
      simp [execMove, MemAccess.regs, paramObjectOf, readReg, hr0, hp.param0Object, scalarsParam,
        loadParamObject, hbits, bind, Except.bind, pure, Except.pure, hal, paramElem,
        Functor.map, Except.map, hoff, DType.width, ParamObjectDecl.bytes]
  · simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Assumptions.paramPointers, Assumptions.sharedBits, Assumptions.deadPackRule,
        h.1] <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
