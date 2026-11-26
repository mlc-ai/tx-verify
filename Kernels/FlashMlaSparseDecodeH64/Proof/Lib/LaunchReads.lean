-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Entry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
public import Lemmas.Flow.Regs
import Lemmas.Flow.LoadShared

@[expose] public section

/-! # The length words a `.nc` load reads

-- domain: consistent

A `.nc` read of four bytes at a length array's row (`ReadsLaunchWord`) at one of the sites of the
assumption `ncReadOnly` returns the launch content (`rebuild_word`): the row's length word
(`rebuild_topk`, `rebuild_extra`). The array's pointer word is the pointer (`pw8_eq`), and the
row's address its 64-bit sum (`lenAddr_eq`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The little-endian number of `n` bytes of `x` from byte `k`. -/
theorem leNat_eq (x : Nat) : ∀ n k, leNat x k n = x / 256 ^ k % 256 ^ n
  | 0, k => by simp [leNat, Nat.mod_one]
  | n + 1, k => by
    rw [leNat, leNat_eq x n (k + 1), pow_succ, Nat.pow_succ, ← Nat.div_div_eq_div_mul,
      Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    simp [leByteOf, BitVec.toNat_ofNat]

/-- A pointer word of `param_0`. -/
theorem pw8_eq (x : Nat) (h : x < 2 ^ 64) : pw8 x = W x := by
  simp only [pw8, leNat_eq, pow_zero, Nat.div_one, W]
  congr 1
  exact Nat.mod_eq_of_lt (by simpa using h)

/-- The address of row `e` of a length array at `x`. -/
theorem lenAddr_eq {x e : Nat} (hx : x + 4 * e < 2 ^ 64) (he : e < 2 ^ 32) :
    add64 (W x) (mulWide .u (W e) 4) = W (x + 4 * e) := by
  apply BitVec.eq_of_toNat_eq
  simp only [add64, mulWide, r64, r32, truncBits, W, i32, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  simp
  omega

/-- A `.nc` read of the four bytes at `addr` at one of the read-only sites. -/
def ReadsLaunchWord (e : Event) (addr : Nat) (bs : List (Option Byte)) : Prop :=
  e.kind = .nc {loc := ⟨.global, 0, addr⟩, size := 4} bs ∧ ncLoads.contains e.pc = true

/-- **A read-only word**: the bytes the read records are the launch content. -/
theorem rebuild_word {X : Execution} {i : EvId} {e : Event} {addr n : Nat}
    {bs : List (Option Byte)} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hget : X.get i = some e) (hr : ReadsLaunchWord e addr bs)
    (hmem : ∀ k < 4, mem0 ⟨.global, 0, addr + k⟩ = some (some (word32Byte n k))) :
    rebuild 3 bs = .ok (b32 n) := by
  have hc := hX.asm Assumptions.ncReadOnly (by simp [Assumptions.all])
  rcases e with ⟨pc, kind⟩
  obtain ⟨he, hsite⟩ := hr
  change kind = _ at he
  subst kind
  obtain ⟨hlen, hbytes⟩ := hc i pc _ bs hget hsite
  have heq : bs = (b32 n).toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 4
    · have hv := hbytes k hk _ (hmem k hk)
      simp only [Execution.initialByte, Option.getD_some, Loc.at] at hv
      rw [hv]
      simp [Value.toBytes, b32, word32Byte, List.getElem?_range hk, Value.bytes]
    · have hb : bs.length = 4 := hlen
      rw [List.getElem?_eq_none (by omega)]
      symm
      apply List.getElem?_eq_none
      simpa [Value.toBytes, b32, Value.bytes] using Nat.le_of_not_gt hk
  rw [heq]
  exact rebuild_scalar (show 0 < 4 by decide) rfl

section
variable {X : Execution} {i : EvId} {e : Event} {x row : Nat} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **The top-k length of a row.** -/
theorem rebuild_topk (hb : row < P.b) (hp : P.topkLenBase = some x) (hget : X.get i = some e)
    (hr : ReadsLaunchWord e (x + 4 * row) bs) : rebuild 3 bs = .ok (b32 (P.topkLen row)) := by
  have hm := hpre.paramTopkLen
  rw [hp] at hm
  obtain ⟨-, -, hmem⟩ := hm
  exact rebuild_word hX hget hr fun k hk => by
    obtain ⟨h, -⟩ := hmem row hb k hk
    simpa [Nat.add_assoc] using h

/-- **The extra top-k length of a row.** -/
theorem rebuild_extra (hb : row < P.b) (hp : P.extraTopkLenBase = some x)
    (hget : X.get i = some e) (hr : ReadsLaunchWord e (x + 4 * row) bs) :
    rebuild 3 bs = .ok (b32 (P.extraTopkLen row)) := by
  have hm := hpre.paramExtraTopkLen
  rw [hp] at hm
  obtain ⟨-, -, hmem⟩ := hm
  exact rebuild_word hX hget hr fun k hk => by
    obtain ⟨h, -⟩ := hmem row hb k hk
    simpa [Nat.add_assoc] using h

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
