-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Segments
public import Kernels.InklingRelDecode.Proof.Lib.RawArith
import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Lemmas.Flow.Arith32Word

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof Arith32

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value} {d : D}
local notation "F" => liveFacts L regs w d
local notation "V" => valueOf L regs w d
local notation "S" => SegU kernel Assumptions.all L g

theorem output_base : S 2427 (F 2427) 2428 (F 2428) :=
  Lib.sum_span false (δ := 256) (by decide) Flow.code_2427 (by decide) (by decide) rfl
    (fun _ _ => ⟨rfl,rfl⟩) (by decide)

theorem qk_base : S 2472 (F 2472) 2473 (F 2473) :=
  Lib.sum_span true (δ := 128 * (d.i % 2)) (by omega) Flow.code_2472 (by decide) (by decide) rfl
    (fun _ h => Lib.delta_reg h (show 551 ∈ Flow.live 2472 by decide) rfl (by omega)) (by decide)

theorem pv_base : S 2523 (F 2523) 2524 (F 2524) :=
  Lib.sum_span true (δ := 128 * ((d.i - 1) % 2)) (by omega) Flow.code_2523
    (by decide) (by decide) rfl
    (fun _ h => Lib.delta_reg h (show 569 ∈ Flow.live 2523 by decide) rfl (by omega)) (by decide)

theorem iter_limit (hw : d.word.regBits.isSome) (hn : d.limit ≤ 2147483646) :
    S 2442 (F 2442) 2443 (F 2443) := by
  apply Lib.sum_span false (δ := 1) (by decide) Flow.code_2442 (by decide) (by decide) _
    (fun _ _ => ⟨rfl,rfl⟩) (by decide)
  change b32 (low d.word + 1) = addBase d.word 1
  change low d.word ≤ 2147483646 at hn
  generalize d.word = v at *
  cases v <;> first | contradiction |
    (change b32 (low _ + 1) = b32 ((low _ + 1) % 2 ^ 32); rw [Nat.mod_eq_of_lt (by omega)])

end PTX.Kernels.InklingRelDecode.Proof.Mma
