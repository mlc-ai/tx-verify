-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.TcCpWs
public import Lemmas.Flow.Step.ShapeAsync
public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part030
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part031
public import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part035

@[expose] public section

/-! # The `tcgen05.cp`, `.ws` MMA and gather4 lemmas at FlashMLA's instructions

`Lemmas/Flow/Step/TcCpWs.lean` at real program counters of `FlashMlaSparseDecodeH64`: the
`tcgen05.cp.cta_group::1.128x256b` at pc 1936, the `tcgen05.mma.ws` with A in Tensor Memory and a
zero-column mask at pc 2027, and the four-row TMA copy (gather4) at pc 2259: each continues at
the next instruction, has the event its shape lemma names, and the MMA's template is its event
from register facts (`tc_mmaTmem`, whose form premises close by `rfl`). -/

namespace PTX.Tests.FlashMlaTcCpWs
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64

variable {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event} {o : Option TState}
  {ins : Instr}

/-- The copy at pc 1936 continues at the next instruction. -/
theorem cp_1936_next (h : kernel.code[1936]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e (some u)) : u = next t := by
  rw [Flow.code_1936] at h
  cases h
  exact fires_tcCp_next hf

/-- The copy at pc 1936 fires a `128x256b` copy without decompression, or faults. -/
theorem cp_1936_shape (h : kernel.code[1936]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∃ s : TcCopy.Spec, s.shape = .s128x256b ∧ s.fmt = none ∧ e = ⟨pc, .tc (.cp s)⟩) ∨
      ∃ f, e = ⟨pc, .ub f⟩ := by
  rw [Flow.code_1936] at h
  cases h
  exact shape_tcCp (P := fun e => (∃ s : TcCopy.Spec, s.shape = .s128x256b ∧ s.fmt = none ∧
      e = ⟨pc, .tc (.cp s)⟩) ∨ ∃ f, e = ⟨pc, .ub f⟩) hf
    (fun s h1 h2 => .inl ⟨s, h1, h2, rfl⟩) fun f => .inr ⟨f, rfl⟩

/-- The `.ws` MMA at pc 2027 continues at the next instruction. -/
theorem mma_2027_next (h : kernel.code[2027]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e (some u)) : u = next t := by
  rw [Flow.code_2027] at h
  cases h
  exact fires_tcMma_next hf

/-- The `.ws` MMA at pc 2027 fires an MMA issue, or faults. -/
theorem mma_2027_shape (h : kernel.code[2027]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∃ d s acc ms, e = ⟨pc, .tc (.mma d s acc ms)⟩) ∨ ∃ f, e = ⟨pc, .ub f⟩ := by
  rw [Flow.code_2027] at h
  cases h
  exact shape_tcMma (P := fun e => (∃ d s acc ms, e = ⟨pc, .tc (.mma d s acc ms)⟩) ∨
      ∃ f, e = ⟨pc, .ub f⟩) hf (fun d s acc ms => .inl ⟨d, s, acc, ms, rfl⟩) fun f => .inr ⟨f, rfl⟩

/-- **The template of the `.ws` MMA at pc 2027** from register facts and decodable descriptors:
its rule, operand forms, mask count and zero-column mask are the instruction's. -/
theorem mma_2027_tmpl (h : kernel.code[2027]? = some ins) {c a a' b i : Nat} {accumulate : Bool}
    (hg : g < L.threads) (hd : t.regs 857 = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs 858 = some (b32 a)) (ha : a < 2 ^ 32) (ho : tmemOffset a 0 = .ok a')
    (hB : t.regs 3077 = some (b64 b)) (hb' : b < 2 ^ 64) (hI : t.regs 859 = some (b32 i))
    (hi : i < 2 ^ 32) (he : mmaEnable t (.reg 4091) = .ok accumulate)
    {db : TcShared.Descriptor} {desc : TcMma.Descriptor} {spec : TcMma.OperandSpec}
    (hdb : TcShared.decode b = some db) (hdi : TcMma.decode .one true .f16 i = some desc)
    (ht : desc.transposeA = false)
    (hs : TcMma.makeOperands L (g / L.block) desc db db = some spec) :
    tcTmpl L g t ins.op =
      .tc (.mma c { spec with aTmem := some a', collector := {} } accumulate [0, 0, 0, 0])
        (next t) := by
  rw [Flow.code_2027] at h
  cases h
  exact tc_mmaTmem (ta := 858) (rB := 3077) (rI := 859) (ms := [0, 0, 0, 0]) rfl rfl rfl rfl hg
    hd hc hA ha ho hB hb' hI hi rfl rfl he zeroColumnMaskOk_imm0 hdb hdi ht hs

/-- The gather4 copy at pc 2259 continues at the next instruction. -/
theorem gather4_2259_next (h : kernel.code[2259]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e (some u)) : u = next t := by
  rw [Flow.code_2259] at h
  cases h
  exact fires_next (by exact trivial) hf

/-- The gather4 copy at pc 2259 issues a tensor copy on the barrier its address names, or
faults. -/
theorem gather4_2259_shape (h : kernel.code[2259]? = some ins) {m : Loc}
    (hm : mbarLoc L g t 696 0 = .ok m)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∃ a s, s.mbar = m ∧ e = ⟨pc, .tensorIssue a s⟩) ∨ ∃ f, e = ⟨pc, .ub f⟩ := by
  rw [Flow.code_2259] at h
  cases h
  exact shape_cpTensorAt (P := fun e => (∃ a s, s.mbar = m ∧ e = ⟨pc, .tensorIssue a s⟩) ∨
      ∃ f, e = ⟨pc, .ub f⟩) hf hm (fun a s hs => .inl ⟨a, s, hs, rfl⟩) fun f => .inr ⟨f, rfl⟩

end PTX.Tests.FlashMlaTcCpWs
