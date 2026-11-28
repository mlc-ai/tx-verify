-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.MoveStep
public import Kernels.InklingRelDecode.Proof.Prologue.QLoadPair
import Lemmas.Flow.OutRun
import Lemmas.Flow.DataCompute

@[expose] public section

/-! # The moves and packs of the query halves

The zero half (`mov.b16` of 0 into register 199), the move of the zero half into each load's
register, and the pack of two halves into a word of a query store. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow

/-- The zero half. -/
def zeroV : Value := .bits 16 0

/-- The halves of a pack: the registers of loads `8 i + 2 k` and `8 i + 2 k + 1`. -/
def pk (i : Fin 8) (k : Fin 4) (b : Fin 2) : Fin 64 := ⟨8 * i.val + 2 * k.val + b.val, by omega⟩

private theorem code_zero : OItem.instrB kernel.code[386]?
    (.move ⟨.scalar, .int .b 16, [some 199], [.imm 0]⟩) = true := by decide +kernel

private theorem code_qmove : ∀ k : Fin 64, OItem.instrB kernel.code[387 + 2 * k.val]?
    (.move ⟨.scalar, .int .u 16, [some (qDst k)], [.reg 199]⟩) = true := by decide +kernel

private theorem code_pack : ∀ i : Fin 8, ∀ k : Fin 4,
    OItem.instrB kernel.code[522 + 6 * i.val + k.val]?
    (.move ⟨.pack, .int .b 32, [some (747 + 5 * i.val + k.val)],
      [.reg (qDst (pk i k 0)), .reg (qDst (pk i k 1))]⟩) = true := by decide +kernel

private theorem side_zero : (Assumptions.emuSites.contains 386 = false ∧
    (Op.move ⟨.scalar, .int .b 16, [some 199], [.imm 0]⟩).isLocal = true ∧
    (MoveInstr.mk .scalar (.int .b 16) [some 199] [.imm 0]).rule = some .threadMove) := by
  decide +kernel

private theorem side_qmove : ∀ k : Fin 64, Assumptions.emuSites.contains (387 + 2 * k.val) = false ∧
    (Op.move ⟨.scalar, .int .u 16, [some (qDst k)], [.reg 199]⟩).isLocal = true ∧
    (MoveInstr.mk .scalar (.int .u 16) [some (qDst k)] [.reg 199]).rule = some .threadMove := by
  decide +kernel

private theorem side_pack : ∀ i : Fin 8, ∀ k : Fin 4,
    Assumptions.emuSites.contains (522 + 6 * i.val + k.val) = false ∧
    (Op.move ⟨.pack, .int .b 32, [some (747 + 5 * i.val + k.val)],
      [.reg (qDst (pk i k 0)), .reg (qDst (pk i k 1))]⟩).isLocal = true ∧
    (MoveInstr.mk .pack (.int .b 32) [some (747 + 5 * i.val + k.val)]
      [.reg (qDst (pk i k 0)), .reg (qDst (pk i k 1))]).rule = some .threadMove := by
  decide +kernel

/-- **The zero half**: the move of 0 into register 199. -/
theorem zero_step {L g} {F : List (Nat × Value)} (hn : 199 ∉ F.map Prod.fst) :
    SegU kernel Assumptions.all L g 386 F 387 ((199, zeroV) :: F) := by
  obtain ⟨h1, h2, h3⟩ := side_zero
  exact Lib.movScalarStep (OItem.instrB_eq code_zero) (by decide) h2 h3 h1
    (by decide) (by decide) (by decide) (fun t _ => rfl) rfl
    (fun R hR => holds_update_cons hR hn)

/-- **The move of the zero half into the register of load `k`.** -/
theorem qmove_step {L g} (k : Fin 64) {F : List (Nat × Value)} (hz : (199, zeroV) ∈ F)
    (hn : qDst k ∉ F.map Prod.fst) :
    SegU kernel Assumptions.all L g (387 + 2 * k.val) F (388 + 2 * k.val)
      ((qDst k, zeroV) :: F) := by
  obtain ⟨h1, h2, h3⟩ := side_qmove k
  have := Lib.movScalarStep (L := L) (g := g) (r := qDst k) (a := .reg 199) (v := zeroV) (F := F)
    (G := (qDst k, zeroV) :: F) (OItem.instrB_eq (code_qmove k)) (by decide) h2 h3 h1
    (by omega) (by omega) (by omega)
    (fun t hF => by simp only [readValue, readReg, holds_mem hF hz]; rfl) rfl
    (fun R hR => holds_update_cons hR hn)
  rwa [show 387 + 2 * k.val + 1 = 388 + 2 * k.val by omega] at this

/-- **The pack of two halves** into word `k` of the query store `i`. -/
theorem pack_step {L g} (i : Fin 8) (k : Fin 4) {F : List (Nat × Value)} {x y : Value}
    (hx : (qDst (pk i k 0), x) ∈ F) (hy : (qDst (pk i k 1), y) ∈ F)
    (hn : 747 + 5 * i.val + k.val ∉ F.map Prod.fst) :
    SegU kernel Assumptions.all L g (522 + 6 * i.val + k.val) F (522 + 6 * i.val + k.val + 1)
      ((747 + 5 * i.val + k.val, joinValue x y) :: F) := by
  obtain ⟨h1, h2, h3⟩ := side_pack i k
  exact Lib.movPackStep (OItem.instrB_eq (code_pack i k)) h2 h3 h1 (by omega) (by omega)
    (by omega) hx hy (fun R hR => holds_update_cons hR hn)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
