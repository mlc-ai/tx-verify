-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.Segments
public import Lemmas.Flow.Havoc
public import Lemmas.Flow.RegBits
import Lemmas.Isa.Rule

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {g pc : Nat} {t : TState} {ii : IntInstr}

theorem intRules (a : Assumption) (ha : a ∈ Assumptions.all) :
    a.localRule L g t (.int ii) = none := by
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

/-- At a worker instruction the integer evaluator determines both the written word
and any fault caused by a register payload with no integer interpretation. -/
theorem workerInt (hr : ii.rule = some .threadInt) (hp : t.pc = pc)
    (hs : Assumptions.emuSites.contains pc = false) :
    execLocalA Assumptions.all L g t (.int ii) = execInt L g t ii := by
  rw [(segFree hs).exec hp,
    execLocalRule_of_none (fun a ha => intRules a ha), execLocal_int hr]

/-- A one-register integer step. The value theorem need only describe successful
evaluation. A failed evaluation gives the terminal alternative in SegU. -/
theorem scalarStepU {F G : List (Nat × Value)} {r : Nat} {v : Value}
    (hc : kernel.code[pc]? = some ⟨none, .int ii⟩)
    (hl : (Op.int ii).isLocal = true) (hr : ii.rule = some .threadInt)
    (hs : Assumptions.emuSites.contains pc = false)
    (hex : ∀ t u, Holds t.regs F → execInt L g t ii = .ok u → u = PTX.next (setReg t r v))
    (hw : ∀ R, Holds R F → Holds (Function.update R r (some v)) G) :
    SegU kernel Assumptions.all L g pc F (pc + 1) G := by
  intro t ht
  obtain ⟨hp, hsub, hacc, hf, hF⟩ := ht
  have heval := workerInt (L := L) (g := g) hr hp hs
  cases he : execInt L g t ii with
  | error fault => exact .inr (dead_of_error (hp ▸ hc) hl hf (heval.trans he))
  | ok u =>
    have htau := tau_of_ok (K := kernel) (hp ▸ hc) hl hf (heval.trans he)
    obtain rfl := hex t u hF he
    exact .inl ⟨_, .single htau, congrArg (· + 1) hp, hsub, hacc, hf, hw _ hF⟩

/-- If an integer register read succeeds, its bits are determined by the stored value. -/
theorem readBits_eq_pattern {r : Nat} {v : Value} {y : BitVec 64}
    (hv : t.regs r = some v) (hy : readBits L g t 32 (.reg r) = .ok y) :
    y = truncBits 32 (v.regBits.getD 0) := by
  cases hx : v.regBits with
  | none =>
    obtain ⟨f, hf⟩ := readBits_regBits_none (w := 32) (L := L) (g := g) hv hx
    rw [hy] at hf
    cases hf
  | some x =>
    rw [readBits_regBits hv hx] at hy
    exact (Except.ok.inj hy).symm

end PTX.Kernels.InklingRelDecode.Proof.Lib
