-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Cnt
public import Lemmas.Flow.Arith32Norm

@[expose] public section

/-! # The MMA warp's reference invariant

The role's events follow one fixed order: the election, the eight Q loads, the arrival on
`bar_q_tma` and its successful poll, the sixteen copies, the commit to `bar_q_utccp` and its
successful poll (the prologue, positions `Site.pro`), then per block `r` the poll of
`bar_dequant_ready[r % 2]`, sixteen MMAs, the commit to `bar_qk_done[r % 2]`, the poll of
`bar_so_ready[r % 2]`, eight MMAs and the commit to `bar_sv_done[r % 2]` (positions `Site.idx`),
and the CTA barrier `12`. The ledger's counts at a state are the counts of that order up to the
state's place (`cntAt`): the prologue's (`proCnt`) and the blocks' (`loopCnt`, with the ring's
uses `ringUses 2 b r` of stage `b` among the first `r` blocks).

The block loop's registers are the block's words (`LoopOk`): the block counter `cnt` is the
block `r`, the phase `pha` is `r % 2`, the parity word `par` is `r / 2 % 2` and the negative
counter `neg` is `r - R` modulo `2 ^ 32`, for the number of blocks `R` the two lengths give
(`rounds`). Before undefined behaviour (the class `ub`) the counts are `cntAt` at the state's
place (`Ref`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-! ### The objects -/

section
variable (L : Launch) (g : Nat)

@[irreducible] def qTmaL : Loc := smLoc L g (qTmaW L) 0
@[irreducible] def qUtL : Loc := smLoc L g (qUtccpW L) 0
@[irreducible] def readyL (b : Nat) : Loc := smLoc L g (readyW L (W b)) 0
@[irreducible] def qkL (b : Nat) : Loc := smLoc L g (qkW L (W b)) 0
@[irreducible] def soL (b : Nat) : Loc := smLoc L g (soW L (W b)) 0
@[irreducible] def svL (b : Nat) : Loc := smLoc L g (svW L (W b)) 0
end

/-- The role's objects as parameters of the counts: the count lemmas see them as variables. -/
structure Objs where
  qTma : Loc
  qUt : Loc
  ready : Nat → Loc
  qk : Nat → Loc
  so : Nat → Loc
  sv : Nat → Loc

/-- The launch's objects. -/
def objs (L : Launch) (g : Nat) : Objs :=
  ⟨qTmaL L g, qUtL L g, readyL L g, qkL L g, soL L g, svL L g⟩

/-! ### Places -/

/-- `1` when `p` holds. -/
abbrev ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- The place of a site in the prologue: the events before it. -/
def Site.pro : Site → Nat
  | .elect => 0
  | .loadTopk | .loadExtra | .trap | .leave _ => 1
  | .qLoad k => 1 + k.val
  | .qArrive => 9
  | .qWait => 10
  | .qFence => 11
  | .qCopy k => 12 + k.val
  | .qCopyCommit => 28
  | .qCopyWait => 29
  | .qCopyFence => 30
  | _ => 31

/-- The place of a site in a block: the block's events before it. -/
def Site.idx : Site → Nat
  | .kvFence => 1
  | .qk k => 2 + k.val
  | .qkCommit => 18
  | .soWait => 19
  | .soFence => 20
  | .pv k => 21 + k.val
  | .pvCommit => 29
  | _ => 0

/-- The MMAs of a block before place `i`. -/
def mmaIn (i : Nat) : Nat :=
  if i < 2 then 0 else if i ≤ 18 then i - 2 else if i ≤ 20 then 16 else i - 5

section
variable (O : Objs)

/-- The prologue's counts before place `j`. -/
def proCnt (j : Nat) : Cnt → Nat
  | .tma => min (j - 1) 8
  | .arrive l => ind (l = O.qTma ∧ 10 ≤ j)
  | .acq l => ind (l = O.qTma ∧ 11 ≤ j) + ind (l = O.qUt ∧ 30 ≤ j)
  | .cp => min (j - 12) 16
  | .commit l => ind (l = O.qUt ∧ 29 ≤ j)
  | .elect => ind (1 ≤ j)
  | _ => 0

/-- The uses of stage `b` among blocks before block `r`, place `i`, from place `k` of a block. -/
def useAt (b r i k : Nat) : Nat := ringUses 2 b r + ind (r % 2 = b ∧ k ≤ i)

/-- The blocks' counts before place `i` of block `r`. -/
def loopCnt (r i : Nat) : Cnt → Nat
  | .acq l =>
    ind (l = O.ready 0) * useAt 0 r i 1 + ind (l = O.ready 1) * useAt 1 r i 1 +
      ind (l = O.so 0) * useAt 0 r i 20 + ind (l = O.so 1) * useAt 1 r i 20
  | .commit l =>
    ind (l = O.qk 0) * useAt 0 r i 19 + ind (l = O.qk 1) * useAt 1 r i 19 +
      ind (l = O.sv 0) * ringUses 2 0 r + ind (l = O.sv 1) * ringUses 2 1 r
  | .mma => 24 * r + mmaIn i
  | _ => 0

/-- **The counts at a place**: prologue place `j`, block `r` at place `i`, and the CTA barrier
when `fin`. -/
def cntAt (j r i : Nat) (fin : Bool) (c : Cnt) : Nat :=
  proCnt O j c + loopCnt O r i c + if fin then ind (c = .bar 12) else 0
end

/-! ### The block loop -/

/-- The blocks the two lengths give (none for a total below 64). -/
def rounds (l0 l1 : BitVec 64) : Nat :=
  if scmpi .lt .s (r27 l0 l1) 64 then 0 else (nblk l0 l1).toNat

/-- The loop registers are block `r`'s words. -/
def LoopOk (d : D) : Prop :=
  let R := rounds d.l0 d.l1
  let r := d.cnt.toNat
  scmpi .lt .s (r27 d.l0 d.l1) 64 = false ∧ 1 ≤ R ∧ R < 2 ^ 26 ∧ r < R ∧ d.cnt = W r ∧
    d.pha = W (r % 2) ∧ d.par = W (r / 2 % 2) ∧ d.neg = W ((2 ^ 32 - R + r) % 2 ^ 32)

/-- A loop site. -/
def Site.inLoop : Site → Bool
  | .kvWait | .kvFence | .qk _ | .qkCommit | .soWait | .soFence | .pv _ | .pvCommit => true
  | _ => false

/-- The role's place facts and counts at a state, before undefined behaviour. -/
def RefCore (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Prop :=
  match d.site with
  | .exit =>
    (∀ c, c ≠ .ub → n c = cntAt (objs L g) 1 0 0 false c) ∨
      ∀ c, c ≠ .ub → n c = cntAt (objs L g) 31 (rounds d.l0 d.l1) 0 true c
  | .outBar => ∀ c, c ≠ .ub → n c = cntAt (objs L g) 31 (rounds d.l0 d.l1) 0 false c
  | s => if s.inLoop then
      LoopOk d ∧ ∀ c, c ≠ .ub → n c = cntAt (objs L g) 31 d.cnt.toNat s.idx false c
    else ∀ c, c ≠ .ub → n c = cntAt (objs L g) s.pro 0 0 false c

/-- **The MMA warp's reference invariant**: before undefined behaviour, the place facts and
counts. -/
def Ref (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Prop := n .ub = 0 → RefCore L g d n

/-- **The sites' launch facts**: a length load's pointer is set, and the hand-back state is the
idle code's first event. -/
def SiteOk (P : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  (d.site = .loadTopk → eqz64 (pw8 (P.topkLenBase.getD 0)) = false) ∧
    (d.site = .loadExtra → eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false) ∧
    ∀ s, d.site = .leave s → s = idleFirst P L g

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
