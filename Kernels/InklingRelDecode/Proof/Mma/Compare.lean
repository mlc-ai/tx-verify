-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Segments
public import Kernels.InklingRelDecode.Proof.Lib.RawArith
import Kernels.InklingRelDecode.Gen.StepMma
import Lemmas.Flow.Arith32Word
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof Arith32

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value} {d : D}
local notation "F" => liveFacts L regs w d
local notation "V" => valueOf L regs w d

theorem limit_check :
    SegU kernel Assumptions.all L g 2425 (F 2425) 2426 (F 2426) := by
  apply Lib.scalarStepU Flow.code_2425 rfl rfl (by decide) (r := 6) (v := V 6)
  · intro t u hF he
    have hv : t.regs 471 = some d.word :=
      holds_mem hF (mem_factsFrom (val := V) (show 471 ∈ Flow.live 2425 by decide))
    have hm : readBits L g t 32 (.imm 2147483646) = .ok 2147483646 := rfl
    simp only [execInt, DType.width, hm, bind, Except.bind, pure, Except.pure] at he
    cases hx : readBits L g t 32 (.reg 471) <;> rw [hx] at he <;> try contradiction
    rw [Lib.readBits_eq_pattern hv hx] at he
    rw [← Except.ok.inj he]
    congr 3
    change decide ((d.limit : Int) > 2147483646) = decide (2147483646 < d.limit)
    simp only [decide_eq_decide]
    omega
  · exact fun _ => Lib.writeLive (val := V) (dst := 6) (rs := Flow.live 2425)
      (rs' := Flow.live 2426) (by decide +kernel)

theorem index_check (hi : d.i < 2 ^ 31) (hn : d.limit < 2 ^ 31) :
    SegU kernel Assumptions.all L g 2455 (F 2455) 2456 (F 2456) := by
  apply Lib.scalarStepU Flow.code_2455 rfl rfl (by decide) (r := 7) (v := V 7)
  · intro t u hF he
    have hv : t.regs 471 = some d.word :=
      holds_mem hF (mem_factsFrom (val := V) (show 471 ∈ Flow.live 2455 by decide))
    have hctr : t.regs 1911 = some (b32 d.i) :=
      holds_mem hF (mem_factsFrom (val := V) (show 1911 ∈ Flow.live 2455 by decide))
    have hbits : readBits L g t 32 (.reg 1911) = .ok (W d.i) := by
      simpa only [r32_W (by omega : d.i < 2 ^ 32)] using
        (readBits_regBits (L := L) (g := g) (w := 32) hctr (show _ = some (W d.i) from rfl))
    simp only [execInt, DType.width, hbits, bind, Except.bind, pure, Except.pure] at he
    cases hx : readBits L g t 32 (.reg 471) <;> rw [hx] at he <;> try contradiction
    rw [Lib.readBits_eq_pattern hv hx] at he
    have repr : truncBits 32 (d.word.regBits.getD 0) = W d.limit := by simp [W,D.limit,low]
    rw [repr] at he
    rw [← Except.ok.inj he]
    congr 3
    change decide (toSigned 32 (W d.i) ≥ toSigned 32 (W d.limit)) = decide (d.limit ≤ d.i)
    rw [toSigned_W hi, toSigned_W hn]
    simp
  · exact fun _ => Lib.writeLive (val := V) (dst := 7) (rs := Flow.live 2455)
      (rs' := Flow.live 2456) (by decide +kernel)

end PTX.Kernels.InklingRelDecode.Proof.Mma
