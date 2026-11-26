-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefLoop
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexWord

@[expose] public section

/-! # The index warp's pair words: the invariant

The words the machine keeps for the loops' pairs (`m0 m1`, `n0 n1`, `e0 e1`, `f0 f1`, the position
word `wpos`) are, at a loop site of block `i` (`Ctr`), the index words of the lane's row at the
block's positions `64 i + 2 lane + el`: the current pair `m` (`MRow`), the next pair `n` once the
next pair's load ran (`NRow`: only when the block is not the loop's last), and the extra loop's
(`ERow`, `FRow`). A pair load's first word is kept in the accumulator (`D.w0`). `IxV d i` is the
site-by-site statement; `ixv_*` are the machine's loop transitions on it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The lane's word `2 lane` of a pair of the row. -/
abbrev lane2 (L : Launch) (g : Nat) : Nat := 2 * (tidOf L g % 32)

/-- The main loop's current pair and position word at block `i`. -/
def MRow (P : Params) (L : Launch) (g : Nat) (c : IxCtl) (i : Nat) : Prop :=
  c.m0 = ixWdM P L g (64 * i + lane2 L g) ∧ c.m1 = ixWdM P L g (64 * i + lane2 L g + 1) ∧
    c.wpos = W (lane2 L g + 1 + 64 * i)

/-- The main loop's next pair at block `i`, when the block is not the last. -/
def NRow (P : Params) (L : Launch) (g : Nat) (c : IxCtl) (i : Nat) : Prop :=
  i + 1 < nMin c.l0 c.l1 → c.n0 = ixWdM P L g (64 * (i + 1) + lane2 L g) ∧
    c.n1 = ixWdM P L g (64 * (i + 1) + lane2 L g + 1)

/-- The extra loop's current pair at its block `b`. -/
def ERow (P : Params) (L : Launch) (g : Nat) (c : IxCtl) (b : Nat) : Prop :=
  c.e0 = ixWdX P L g (64 * b + lane2 L g) ∧ c.e1 = ixWdX P L g (64 * b + lane2 L g + 1)

/-- The extra loop's next pair at block `i`, when the block is not the last. -/
def FRow (P : Params) (L : Launch) (g : Nat) (c : IxCtl) (i : Nat) : Prop :=
  i + 1 < roundsOf c.l0 c.l1 →
    c.f0 = ixWdX P L g (64 * (i + 1 - nMain c.l0) + lane2 L g) ∧
      c.f1 = ixWdX P L g (64 * (i + 1 - nMain c.l0) + lane2 L g + 1)

/-- **The pair words at a state in block `i`.** -/
def IxV (P : Params) (L : Launch) (g : Nat) (d : D) (i : Nat) : Prop :=
  match d.site with
  | .pre => d.el = 1 → d.w0 = ixWdM P L g (lane2 L g)
  | .pf => MRow P L g d.c i ∧ (d.el = 1 → d.w0 = ixWdM P L g (64 * (i + 1) + lane2 L g))
  | .wA | .sA1 | .sA2 | .stA | .bA | .arrA => MRow P L g d.c i ∧ NRow P L g d.c i
  | .xpre => d.el = 1 → d.w0 = ixWdX P L g (lane2 L g)
  | .xpf => ERow P L g d.c (i - nMain d.c.l0) ∧
      (d.el = 1 → d.w0 = ixWdX P L g (64 * (i + 1 - nMain d.c.l0) + lane2 L g))
  | .wB | .sB1 | .sB2 | .stB | .bB | .arrB => ERow P L g d.c (i - nMain d.c.l0) ∧ FRow P L g d.c i
  | _ => True

/-- **The word a pair load of the state returns**, for block `i`. -/
def ixLdWord (P : Params) (L : Launch) (g : Nat) (d : D) (i : Nat) : BitVec 64 :=
  match d.site with
  | .pre => ixWdM P L g (lane2 L g + d.el)
  | .pf => ixWdM P L g (64 * (i + 1) + lane2 L g + d.el)
  | .xpre => ixWdX P L g (lane2 L g + d.el)
  | _ => ixWdX P L g (64 * (i + 1 - nMain d.c.l0) + lane2 L g + d.el)

/-- The sites before the loops' blocks, after the loops and the exit: no word to keep. -/
def Vac : IxSite → Prop
  | .lenA | .lenB | .pre | .xpre | .bar | .exit => True
  | _ => False

/-- A state at the first element of a site without words satisfies the invariant. -/
theorem ixv_vac {p : IxSite × IxCtl} {i : Nat} (h : Vac p.1) : IxV P L g (ofC p) i := by
  obtain ⟨s, c⟩ := p
  cases s <;> simp only [Vac] at h <;> simp [IxV, ofC]

theorem vac_ixMainDone (c : IxCtl) : Vac (ixMainDone c).1 := by
  unfold ixMainDone; dsimp only; split <;> simp [Vac]

theorem vac_ixNoMain (c : IxCtl) : Vac (ixNoMain c).1 := by
  unfold ixNoMain; exact vac_ixMainDone _

theorem vac_ixLens (c : IxCtl) : Vac (ixLens c).1 := by
  unfold ixLens; dsimp only; split
  · exact vac_ixNoMain _
  · simp [Vac]

theorem vac_ixAfterA (P : Params) (c : IxCtl) : Vac (ixAfterA P c).1 := by
  unfold ixAfterA; split
  · exact vac_ixLens _
  · simp [Vac]

theorem vac_ixFirst (P : Params) (L : Launch) (g : Nat) : Vac (ixFirst P L g).1 := by
  unfold ixFirst; dsimp only; split
  · simp [Vac]
  · split
    · exact vac_ixAfterA _ _
    · simp [Vac]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
