-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Cnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StCount
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Objs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefArith

@[expose] public section

/-! # The index warp's reference invariant

The counts of the role's ledger (`Cnt.lean`) at each state, before any undefined behaviour: the
state is in block `i` of the ring (the main cache's blocks, then the extra cache's, one ring):
the slot is `i % 4`, the parity bit `i / 4 % 2`, and each slot `s` was polled (`coordFree s`)
and arrived on (`coordReady s`) once per earlier block that used it (`ringUses 4 s i`), the poll
of block `i` counted from its success on (`incW`). Before the loops (`preSite`: the length
loads and the first index pair) the block is `0`.

The loops' counters against the block (`Ctr`, over the state's own length words `l0`, `l1`, with
the main cache's blocks `M = nMain l0`, the total `R = roundsOf l0 l1` and the main loop's
`min M R`, `RefArith.lean`): a main block `i` is below `min M R`, with the counter `i + 1` and
the negative counter `i - min M R` (`MainW`); the extra cache's first pair is at block `M < R`;
an extra block `i` is between `M` and `R`, with the counter `i + 1` and the negative counter
`i - R` (`XW`); the barrier and the exit are at block `R`.

The writes (`StEq`, `StCount.lean`): the class `st` counts `(2 + [lane % 4 = 0]) i` writes for the
`i` finished blocks and the state's own.

The transitions' ring words (`Keeps`): the loops' heads, the main loop's exit and the extra
loop's entry keep the slot and parity and lead to a site before a poll; the blocks' ends advance
the slot and the parity (`ixParNext`); the set-up's transitions keep the zero ring. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The poll of the current block has succeeded (the sites after it, up to the arrival). -/
def incW : IxSite → Nat
  | .sA1 | .sA2 | .stA | .bA | .arrA | .sB1 | .sB2 | .stB | .bB | .arrB => 1
  | _ => 0

/-- A site that has made no store of its block. -/
theorem stDone_incW {s : IxSite} (h : incW s = 0) (el : Nat) : stDone L g s el = 0 := by
  cases s <;> first | rfl | exact absurd h (by decide)

/-- The sites before the loops. -/
def preSite : IxSite → Bool
  | .lenA | .lenB | .pre => true
  | _ => false

/-- Block `i` of the main loop: below the main loop's count, the counter `i + 1`, the negative
counter `i - min M R`, the extra loop's counter at the main cache's blocks and the next pair's
address `256 (i + 1)` bytes above the lane's first pair's (`ixApB`). -/
def MainW (P : Params) (L : Launch) (g : Nat) (c : IxCtl) (i : Nat) : Prop :=
  i < nMin c.l0 c.l1 ∧ c.cnt = W (i + 1) ∧
    c.neg = W ((2 ^ 32 - nMin c.l0 c.l1 + i) % 2 ^ 32) ∧ c.xb = W (nMain c.l0) ∧
    c.aptr = ixApB P L g + W (256 * (i + 1))

/-- Block `i` of the extra loop: between the main cache's blocks and the total, the counter
`i + 1`, the negative counter `i - R` and the next pair's position word `64 (i - M)` above its
first value (`ixXa0`). -/
def XW (L : Launch) (g : Nat) (c : IxCtl) (i : Nat) : Prop :=
  nMain c.l0 < roundsOf c.l0 c.l1 ∧ nMain c.l0 ≤ i ∧ i < roundsOf c.l0 c.l1 ∧
    c.xb = W (i + 1) ∧ c.xn = W ((2 ^ 32 - roundsOf c.l0 c.l1 + i) % 2 ^ 32) ∧
    c.xa = W (((ixXa0 L g).toNat + 64 * (i - nMain c.l0)) % 2 ^ 32)

/-- **The loops' counters at site `s` in block `i`**; a pair load of the next block (`pf`,
`xpf`) is made only below the loop's count. -/
def Ctr (P : Params) (L : Launch) (g : Nat) : IxSite → IxCtl → Nat → Prop
  | .lenA, _, _ | .lenB, _, _ => True
  | .pre, c, _ => c.xb = W (nMain c.l0)
  | .xpre, c, i => nMain c.l0 < roundsOf c.l0 c.l1 ∧ i = nMain c.l0 ∧ c.xb = W (nMain c.l0)
  | .bar, c, i | .exit, c, i => i = roundsOf c.l0 c.l1
  | .pf, c, i => MainW P L g c i ∧ i + 1 < nMin c.l0 c.l1
  | .wA, c, i | .sA1, c, i | .sA2, c, i | .stA, c, i | .bA, c, i | .arrA, c, i =>
    MainW P L g c i
  | .xpf, c, i => XW L g c i ∧ i + 1 < roundsOf c.l0 c.l1
  | .wB, c, i | .sB1, c, i | .sB2, c, i | .stB, c, i | .bB, c, i | .arrB, c, i =>
    XW L g c i

/-- The ring's counts at block `i` (`w`: the current poll's success). -/
def RingCounts (L : Launch) (g : Nat) (n : Cnt → Nat) (i w : Nat) : Prop :=
  ∀ s : Fin 4, n (.acq (MbarRow.loc L g (.coordFree s))) = ringUses 4 s.val (i + w) ∧
    n (.arrive (MbarRow.loc L g (.coordReady s))) = ringUses 4 s.val i

/-- The invariant's body: block `i`, its ring words, the counts and the loops' counters. -/
def Body (P : Params) (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Prop :=
  ∃ i, (preSite d.site = true → i = 0) ∧ d.c.slot = MbarRow.slot4 i ∧
    d.c.par = decide (i / 4 % 2 = 1) ∧ RingCounts L g n i (incW d.site) ∧ Ctr P L g d.site d.c i ∧
    StEq L g d n i

/-- **The reference invariant** of a state with counts `n`, before undefined behaviour. -/
def Ref (P : Params) (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Prop :=
  n .ub = 0 → Body P L g d n

/-! ### The ring's arithmetic -/

/-- The four slots' uses before block `i` are `i`. -/
theorem ring_sum (i : Nat) :
    ringUses 4 0 i + ringUses 4 1 i + ringUses 4 2 i + ringUses 4 3 i = i := by
  simp only [ringUses]; omega

/-- The uses of block `i`'s slot before it are `i / 4`. -/
theorem ring_here (i : Nat) : ringUses 4 (MbarRow.slot4 i).val i = i / 4 :=
  ringUses_here rfl (Nat.mod_lt _ (by decide))

/-- Block `i` uses slot `i % 4` once more. -/
theorem ring_succ (s : Fin 4) (i : Nat) :
    ringUses 4 s.val (i + 1) = ringUses 4 s.val i + if MbarRow.slot4 i = s then 1 else 0 := by
  rw [ringUses_succ s.isLt]
  simp only [MbarRow.slot4, Fin.ext_iff]

/-- The slot after block `i`'s. -/
theorem slot_succ (i : Nat) : MbarRow.slot4 i + 1 = MbarRow.slot4 (i + 1) := by
  simp only [MbarRow.slot4, Fin.ext_iff, Fin.val_add]; omega

/-- The parity after block `i`'s. -/
theorem par_succ (i : Nat) :
    ixParNext (decide (i / 4 % 2 = 1)) (MbarRow.slot4 i) = decide ((i + 1) / 4 % 2 = 1) := by
  simp only [ixParNext, MbarRow.slot4, Fin.ext_iff]
  by_cases h : i % 4 = 3
  · have : (i + 1) / 4 = i / 4 + 1 := by omega
    simp only [h, this]
    rcases Nat.mod_two_eq_zero_or_one (i / 4) with h2 | h2 <;> simp [h2] <;> omega
  · have : (i + 1) / 4 = i / 4 := by omega
    simp [h, this]

/-! ### The transitions' ring words -/

/-- A transition result keeps the words' ring `c` and leads to a site before a poll. -/
def Keeps (c : IxCtl) (p : IxSite × IxCtl) : Prop :=
  p.2.slot = c.slot ∧ p.2.par = c.par ∧ incW p.1 = 0 ∧ preSite p.1 = false

theorem keeps_mainTop (c : IxCtl) : Keeps c (mainTop c) := by
  unfold mainTop; dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem keeps_mainDone (c : IxCtl) : Keeps c (ixMainDone c) := by
  unfold ixMainDone; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem keeps_xTop (c : IxCtl) : Keeps c (xTop c) := by
  unfold xTop; dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem keeps_afterXpre (c : IxCtl) : Keeps c (afterXpre L g c) := by
  unfold afterXpre; split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact keeps_xTop _

/-- A block's end: the next slot and parity. -/
theorem keeps_mainEnd (c : IxCtl) :
    Keeps { c with par := ixParNext c.par c.slot, slot := c.slot + 1 } (mainEnd c) := by
  unfold mainEnd; dsimp only; split
  · exact keeps_mainTop _
  · exact keeps_mainDone _

theorem keeps_xEnd (c : IxCtl) :
    Keeps { c with par := ixParNext c.par c.slot, slot := c.slot + 1 } (xEnd c) := by
  unfold xEnd; dsimp only; split
  · exact keeps_xTop _
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- A set-up result: the zero ring, before a poll. -/
def Zero (p : IxSite × IxCtl) : Prop := p.2.slot = 0 ∧ p.2.par = false ∧ incW p.1 = 0

theorem zero_noMain (c : IxCtl) : Zero (ixNoMain c) := by
  unfold ixNoMain
  obtain ⟨h1, h2, h3, -⟩ := keeps_mainDone { c with slot := 0, par := false }
  exact ⟨h1, h2, h3⟩

theorem zero_afterPre (c : IxCtl) : Zero (afterPre P L g c) := by
  unfold afterPre; split
  · exact zero_noMain _
  · unfold mainEntry
    obtain ⟨h1, h2, h3, -⟩ := keeps_mainTop
      _
    exact ⟨h1, h2, h3⟩

theorem zero_lens {c : IxCtl} (h1 : c.slot = 0) (h2 : c.par = false) : Zero (ixLens c) := by
  unfold ixLens; dsimp only; split
  · exact zero_noMain _
  · exact ⟨h1, h2, rfl⟩

theorem zero_afterA (P : Params) {c : IxCtl} (h1 : c.slot = 0) (h2 : c.par = false) :
    Zero (ixAfterA P c) := by
  unfold ixAfterA; split
  · exact zero_lens h1 h2
  · exact ⟨h1, h2, rfl⟩

theorem zero_first (P : Params) (L : Launch) (g : Nat) : Zero (ixFirst P L g) := by
  unfold ixFirst; dsimp only; split
  · exact ⟨rfl, rfl, rfl⟩
  · split
    · exact zero_afterA P rfl rfl
    · exact ⟨rfl, rfl, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
