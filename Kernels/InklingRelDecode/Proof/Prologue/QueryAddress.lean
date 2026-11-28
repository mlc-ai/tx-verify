-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Values
public import Kernels.InklingRelDecode.Proof.Lib.QTile
public import Kernels.InklingRelDecode.Spec
import Lemmas.Flow.Arith32Word
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Proof PTX.Flow Arith32 Control

set_option maxRecDepth 8192

private theorem swizzle : ∀ t : Fin 256,
    xor32 (andi (shl (W t.val) 4) 2032) (andi (shl (W t.val) 1) 112) = W (Lib.qSwz t.val) ∧
    Lib.qSwz t.val + 16 ≤ 2048 := by decide +kernel

/-- Base of one lane's four consecutive words within the group's query tile. -/
def queryAddress (L : Launch) (g : Nat) (i : Fin 8) :=
  L.sharedBase + Lib.qSwz (g%L.block) + (196608 + 2048 * Lib.qGroup i)

theorem queryAddress_range {Q L m} (hp : Pre Q L m) (g : Nat) (i : Fin 8) :
    L.sharedBase+196608 ≤ queryAddress L g i ∧ queryAddress L g i+16 ≤ L.sharedBase+212992 := by
  have ht : g%L.block < 256 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have sw : Lib.qSwz (g%L.block) + 16 ≤ 2048 := (swizzle ⟨_,ht⟩).2
  have gr := Lib.qGroup_lt i i.isLt
  unfold queryAddress
  omega

theorem query_register {Q L m g w d} (hp : Pre Q L m) (i : Fin 8) :
    valueOf Q L g w d (746+5*i.val) = b32 (queryAddress L g i) := by
  have reg : ∀ i : Fin 8, valueOf Q L g w d (746+5*i.val) =
      .bits 32 (addi (queryBase L (g%L.block)) ((196608 + 2048 * Lib.qGroup i : Nat) : Int)) := by
    intro i
    fin_cases i <;> simp only [Lib.qGroup] <;> norm_num1 <;> rfl
  have room := hp.sharedRange
  unfold sharedBytes at room
  have ht : g%L.block < 256 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have sw := swizzle ⟨_,ht⟩
  dsimp only at sw
  have gr := Lib.qGroup_lt i i.isLt
  have bound := (queryAddress_range hp g i).2
  unfold queryAddress at bound ⊢
  rw [reg,queryBase,sw.1,Nat.mod_eq_of_lt (show L.sharedBase < 2^32 by omega),
    add32_W (by omega),addi_W (by omega) (by omega)]
  rfl

end PTX.Kernels.InklingRelDecode.Proof.Prologue
