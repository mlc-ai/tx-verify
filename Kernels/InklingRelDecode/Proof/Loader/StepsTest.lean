-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.StepsBack
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section

private theorem inc_eq_of_read {L : Launch} {g : Nat} {t : TState} {i : Value} {x : BitVec 64}
    (hi : t.regs 1905 = some (incValue i)) (hx : readBits L g t 32 (.reg 1905) = .ok x) :
    incValue i = nextCounter i := by
  cases hv : (incValue i).regBits with
  | some v => exact inc_bits hv
  | none =>
    obtain ⟨_, hf⟩ := readBits_regBits_none (L := L) (g := g) (w := 32) hi hv
    rw [hx] at hf
    cases hf

private theorem replace_self (V : Nat → Value) : replaceCounter V (V 1905) = V := by
  funext r
  by_cases h : r = 1905
  · subst r
    rfl
  · simp [replaceCounter, List.lookup, beq_eq_false_iff_ne.mpr h]

/-- The back edge tests the incremented register against the second word of the
vector load. A successful comparison also establishes that the register now has integer kind. -/
theorem test_span {L : Launch} {g : Nat} (i n : Value) (V : Nat → Value)
    (hi : V 1905 = nextCounter i) (hn : V 467 = n) :
    SegU kernel Assumptions.all L g 2417
      (factsFrom (Flow.live 2417) (replaceCounter V (incValue i))) 2418
      ((25, .pred (decide (r32 (bits i + 1) ≠ bits n))) :: factsFrom (Flow.live 2417) V) := by
  intro t ht
  obtain ⟨hp, hs, ha, hflt, hR⟩ := ht
  let op : IntInstr := ⟨.setp .ne none, .int .b 32, false, [some 25], [.reg 467, .reg 1905]⟩
  have hc : kernel.code[t.pc]? = some ⟨none, .int op⟩ := hp ▸ Flow.code_2417
  have heval := Lib.workerInt (ii := op) (L := L) (g := g) (by rfl) hp (by decide)
  cases hh : execInt L g t op with
  | error f => exact .inr (dead_of_error hc rfl hflt (heval.trans hh))
  | ok u =>
    have ri : t.regs 1905 = some (incValue i) :=
      holds_mem hR (mem_factsFrom (show 1905 ∈ Flow.live 2417 by decide))
    have rn : t.regs 467 = some n := by
      rw [← hn]
      exact holds_mem hR (mem_factsFrom (show 467 ∈ Flow.live 2417 by decide))
    have hτ := tau_of_ok hc rfl hflt (heval.trans hh)
    simp only [op, execInt, DType.width, bind, Except.bind, pure, Except.pure] at hh
    cases hn' : readBits L g t 32 (.reg 467) <;> rw [hn'] at hh <;> try contradiction
    cases hi' : readBits L g t 32 (.reg 1905) <;> rw [hi'] at hh <;> try contradiction
    have he := inc_eq_of_read ri hi'
    rw [he] at ri
    rw [Lib.readBits_eq_pattern rn hn', Lib.readBits_eq_pattern ri hi'] at hh
    obtain rfl := Except.ok.inj hh
    have hcmp : compare .ne .b 32 (bits n) (bits (nextCounter i)) =
        decide (r32 (bits i + 1) ≠ bits n) := by
      rw [show bits (nextCounter i) = r32 (bits i + 1) from truncBits_idem ..]
      simp only [PTX.compare, decide_eq_decide, ne_eq, Int.ofNat_inj, BitVec.toNat_inj]
      exact not_congr eq_comm
    rw [he, ← hi, replace_self] at hR
    refine .inl ⟨_, .single hτ, congrArg (· + 1) hp, hs, ha, hflt, ?_⟩
    refine ⟨?_,
      holds_update hR (by fact_free)⟩
    simpa only [PTX.next, setReg, Function.update_self, DType.kind?, Option.getD_some, bits] using
      congrArg (fun b => some (Value.pred b)) hcmp

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
