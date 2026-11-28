-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Cnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Objs
public import Lemmas.Flow.Arith32Word

@[expose] public section

/-! # Warpgroup 2's reference invariant

The counts of the role's ledger (`Cnt.lean`) at each state, before any undefined behaviour:

* in the set-up (`smr` to the Q poll `wq`): no successful poll of `qUtccp` and no use of the
  slots' barriers yet;
* in block `i` of the loop (`wraw` to the raw-free arrival `arrF`): the slot bit is `i % 2`, the
  parity bit `i / 2 % 2`, and each slot `b`'s count of successful polls of `rawReady b` and
  `svDone b` and of arrivals on `dequantReady b` and `rawFree b` is its uses before block `i`
  (`uses b i`), plus one for the uses of block `i` the site has passed (`incR`, ...); the
  block counter `cnt` is `i - R` modulo `2 ^ 32` for the block count `R` of the two lengths
  (`rounds`, `LoopWords`), and `i < R`;
* at the closing barrier (`bar`) and the exit after it: every slot count is its uses among all
  `R` blocks (the loop exits exactly after the last block, or at once when there is none; the
  early exit of a CTA beyond the batch does not happen, `batch_in`).

The counts on `n` are the thread's prefix counts (the glued ledger, `Common/Roles.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-- The blocks before block `i` that used slot `b`. -/
def uses (b : Fin 2) (i : Nat) : Nat := (i + 1 - b.val) / 2

/-- The barrier uses of the block a site has passed (`0` or `1` each): the raw-ready poll
(`incR`), the SV-done poll (`incS`), the dequant-ready arrival (`incD`), the raw-free arrival
(`incF`). -/
def incR : Site → Nat
  | .wraw => 0
  | _ => 1
def incS : Site → Nat
  | .wraw | .wsv => 0
  | _ => 1
def incD : Site → Nat
  | .arrF => 1
  | _ => 0
def incF (_ : Site) : Nat := 0

/-- The blocks the two lengths give (none for a padded total below 64). -/
def rounds (l0 l1 : BitVec 64) : Nat :=
  if scmpi .lt .s (r57 l0 l1) 64 then 0 else (nblk l0 l1).toNat

/-- The block counter of block `i`: `i - R` modulo `2 ^ 32`, with `i < R < 2 ^ 26`. -/
def LoopWords (d : D) (i : Nat) : Prop :=
  i < rounds d.l0 d.l1 ∧ rounds d.l0 d.l1 < 2 ^ 26 ∧
    d.cnt = W ((2 ^ 32 - rounds d.l0 d.l1 + i) % 2 ^ 32)

/-- The four barrier counts of slot `b` are the uses `a`, `s`, `r`, `f`. -/
def SlotCounts (L : Launch) (g : Nat) (n : Cnt → Nat) (b : Fin 2) (a s r f : Nat) : Prop :=
  n (.acq (MbarRow.loc L g (.rawReady b))) = a ∧ n (.acq (MbarRow.loc L g (.svDone b))) = s ∧
    n (.arrive (MbarRow.loc L g (.dequantReady b))) = r ∧
    n (.arrive (MbarRow.loc L g (.rawFree b))) = f

/-- The loop's counts at block `i`. -/
def LoopCounts (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) (i : Nat) : Prop :=
  d.sb = decide (i % 2 = 1) ∧ d.pb = decide (i / 2 % 2 = 1) ∧
    ∀ b, SlotCounts L g n b (uses b (i + incR d.site)) (uses b (i + incS d.site))
      (uses b (i + incD d.site)) (uses b (i + incF d.site))

/-- **The reference invariant** of a state with counts `n`, before undefined behaviour. -/
def Ref (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Prop :=
  n .ub = 0 →
    match d.site with
    | .smr | .lenA | .lenB | .wq =>
      n (.acq (MbarRow.loc L g .qUtccp)) = 0 ∧ ∀ b, SlotCounts L g n b 0 0 0 0
    | .bar => ∀ b, SlotCounts L g n b (uses b (rounds d.l0 d.l1)) (uses b (rounds d.l0 d.l1))
        (uses b (rounds d.l0 d.l1)) (uses b (rounds d.l0 d.l1))
    | .exit => ∀ b, SlotCounts L g n b (uses b (rounds d.l0 d.l1)) (uses b (rounds d.l0 d.l1))
        (uses b (rounds d.l0 d.l1)) (uses b (rounds d.l0 d.l1))
    | _ => ∃ i, LoopWords d i ∧ LoopCounts L g d n i

/-! ### The ring's arithmetic -/

/-- The two slots' uses before block `i` are `i`. -/
theorem uses_sum (i : Nat) : uses 0 i + uses 1 i = i := by
  simp only [uses, Fin.val_zero, Fin.val_one]; omega

/-- The slot bit of block `i` is its ring slot. -/
theorem slotF_slot2 (i : Nat) : slotF (decide (i % 2 = 1)) = MbarRow.slot2 i := by
  unfold slotF MbarRow.slot2
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

/-- The uses of block `i`'s slot before it are `i / 2`. -/
theorem uses_slot (i : Nat) : uses (MbarRow.slot2 i) i = i / 2 := by
  simp only [uses, MbarRow.slot2]; omega

/-- A parity bit's word reads as the bit. -/
theorem rawPar_bit (p : Bool) : (truncBits 32 (rawPar p)).toNat % 2 = if p then 1 else 0 := by
  cases p <;> decide

theorem svPar_bit (p : Bool) : (truncBits 32 (svPar p)).toNat % 2 = if p then 0 else 1 := by
  cases p <;> decide

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
