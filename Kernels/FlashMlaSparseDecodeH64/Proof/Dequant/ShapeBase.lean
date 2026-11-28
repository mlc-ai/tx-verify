-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ev
public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.Step.ShapeTc
public import Lemmas.Flow.Step.ShapeAsync
public import Lemmas.Flow.Step.Record
public import Lemmas.Flow.Next
public import Lemmas.Flow.Step.SegSym

@[expose] public section

/-! # Helpers for warpgroup 2's shape obligations

`ring_m8`: a slot's barrier word is 8-byte aligned; `readW`: a register read of a stated word;
the tactics `dq_open` (open one site's obligation: the facts `hF`, the pc `hpc`, the sub-step
`hsub`, the instruction by its lookup, the table's row) and `rg r` (a register's fact). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A slot's barrier word, `c` above the slot's 8-byte step from the shared base (`c` a multiple
of 8), is 8-byte aligned. -/
theorem ring_m8 (hp : Pre P L m) (b : Bool) {c : Nat} (hc : c % 8 = 0) :
    (truncBits 32 (truncBits 32 (addi (r2330W L b) c) + BitVec.ofInt 64 0)).toNat % 8 = 0 := by
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  have h3 := hp.sharedRange
  unfold sharedBytes at h3
  have hs : shl (slW b) 3 = BitVec.ofNat 64 (if b then 8 else 0) := by cases b <;> decide
  simp only [r2330W, hs]
  cases b <;>
  simp only [add32, addi, r32, i32, sbw, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A 32-bit read of a register holding a word. -/
theorem readW {t : TState} {r w : Nat} {x : BitVec 64} (h : t.regs r = some (.bits w x)) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure]

set_option hygiene false in
/-- Open the shape obligation of a concrete site. -/
macro "dq_open" : tactic => `(tactic| (
  intro t ins e o hat hi hc hf
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  try dsimp only [Flow.Code.AtD, code, facts, Site.pc, rowBase, Fin.isValue, Fin.val_zero,
    Fin.val_one, Fin.val_two] at hpc hsub hc hF ⊢
  try simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte, Nat.reduceLT,
    Nat.reduceEqDiff, Fin.isValue, Fin.val_ofNat, Nat.reduceMod] at hpc hc hF ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  try simp only [EvK, PollEv, LoadEv, StoreEv]))

set_option hygiene false in
/-- A register's fact at an opened site. -/
macro "rg " r:num : term => `(regs_of_factsFrom hF (r := $r) (by decide +kernel))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
