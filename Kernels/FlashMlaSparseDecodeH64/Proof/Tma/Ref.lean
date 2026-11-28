-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Cnt
public import Lemmas.Flow.Arith32Norm

@[expose] public section

/-! # The TMA warp's reference invariant

The role's events follow one fixed order: the election, the successful polls of `bar_q_utccp` and
of `bar_last_store_done` (the prologue, places `Site.pro`), then per block `r` the successful
polls of `valid_coord_ready[r % 4]` and `raw_free[r % 2]`, the 64 coordinate reads interleaved
with the 16 gathers, the arrival on `raw_ready[r % 2]` and the arrival on `valid_coord_free[r % 4]`
(a block's place: its stage `Site.stage` among the four mbarrier events, the reads `Site.rdN`
and the gathers `Site.gN` before it), and the CTA barrier `12`. The ledger's counts at a state
are the counts of that order up to the state's place (`cntAt`), with the ring's uses
`ringUses S b r` of slot `b` among the first `r` blocks (`S = 4` for the coordinate ring, `2` for
the raw tile).

The loop's registers are block `r`'s words (`LoopOk`): the block counter is `r`, the tile slot
`r % 2`, the ring slot `r % 4`, the tile's parity word `r / 2 % 2`, the ring's `r / 4 % 2` and the
negative counter `r - R` modulo `2 ^ 32`, for the block count `R` of the two lengths (`rounds`).
Before undefined behaviour the counts are `cntAt` at the state's place (`Ref`). The objects are a
parameter of the counts (`Objs`), so no count lemma compares two locations. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-! ### The objects -/

section
variable (L : Launch) (g : Nat)

@[irreducible] def qUtL : Loc := smLoc L g (qUtW L) 0
@[irreducible] def lastL : Loc := smLoc L g (lastW L) 0
@[irreducible] def readyL (b : Nat) : Loc :=
  smLoc L g (addi (add32 (sbw L) (shl (W b) 3)) 222840) 0
@[irreducible] def freeL (b : Nat) : Loc :=
  smLoc L g (addi (add32 (sbw L) (shl (W b) 3)) 222824) 0
@[irreducible] def rawL (b : Nat) : Loc :=
  smLoc L g (addi (add32 (sbw L) (shl (W b) 3)) 222808) 0
@[irreducible] def cfreeL (b : Nat) : Loc :=
  smLoc L g (addi (mad32 (W b) (i32 (-248)) (mad32 (W b) (i32 248)
    (add32 (sbw L) (shl (W b) 3)))) 222872) 0
end

/-- The role's objects as parameters of the counts. -/
structure Objs where
  qUt : Loc
  last : Loc
  ready : Nat → Loc
  free : Nat → Loc
  raw : Nat → Loc
  cfree : Nat → Loc

/-- The launch's objects. -/
def objs (L : Launch) (g : Nat) : Objs :=
  ⟨qUtL L g, lastL L g, readyL L g, freeL L g, rawL L g, cfreeL L g⟩

/-! ### Places -/

/-- `1` when `p` holds. -/
abbrev ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- The place of a site in the prologue: the prologue's events before it. -/
def Site.pro : Site → Nat
  | .elect => 0
  | .loadTopk | .loadExtra | .qWait | .leave _ => 1
  | .storeWait => 2
  | _ => 3

/-- A block's mbarrier events before a site: the ring's poll, the tile's poll, the tile's
arrival. -/
def Site.stage : Site → Nat
  | .rawWait => 1
  | .coord0 _ | .coord1 _ | .coord2 _ | .coord3 _ | .gather _ | .rawArrive => 2
  | .coordFree => 3
  | _ => 0

/-- A block's coordinate reads before a site. -/
def Site.rdN : Site → Nat
  | .coord0 k => 4 * k.val
  | .coord1 k => 4 * k.val + 1
  | .coord2 k => 4 * k.val + 2
  | .coord3 k => 4 * k.val + 3
  | .gather k => if k.val = 15 then 64 else 4 * k.val + 8
  | .rawArrive | .coordFree => 64
  | _ => 0

/-- A block's gathers before a site. -/
def Site.gN : Site → Nat
  | .coord0 k | .coord1 k | .coord2 k | .coord3 k => k.val - 1
  | .gather k => k.val
  | .rawArrive | .coordFree => 16
  | _ => 0

section
variable (O : Objs)

/-- The prologue's counts before place `j`. -/
def proCnt (j : Nat) : Cnt → Nat
  | .acq l => ind (l = O.qUt ∧ 2 ≤ j) + ind (l = O.last ∧ 3 ≤ j)
  | .elect => ind (1 ≤ j)
  | _ => 0

/-- The uses of slot `b` of a ring of `S` among blocks before block `r` at stage `i`, counting
block `r`'s from stage `k`. -/
def useAt (S b r i k : Nat) : Nat := ringUses S b r + ind (r % S = b ∧ k ≤ i)

/-- The blocks' counts before stage `i`, read `rd` and gather `gs` of block `r`. -/
def loopCnt (r i rd gs : Nat) : Cnt → Nat
  | .acq l =>
    ind (l = O.ready 0) * useAt 4 0 r i 1 + ind (l = O.ready 1) * useAt 4 1 r i 1 +
      ind (l = O.ready 2) * useAt 4 2 r i 1 + ind (l = O.ready 3) * useAt 4 3 r i 1 +
      ind (l = O.free 0) * useAt 2 0 r i 2 + ind (l = O.free 1) * useAt 2 1 r i 2
  | .arrive l =>
    ind (l = O.raw 0) * useAt 2 0 r i 3 + ind (l = O.raw 1) * useAt 2 1 r i 3 +
      ind (l = O.cfree 0) * ringUses 4 0 r + ind (l = O.cfree 1) * ringUses 4 1 r +
      ind (l = O.cfree 2) * ringUses 4 2 r + ind (l = O.cfree 3) * ringUses 4 3 r
  | .gather l =>
    ind (l = O.raw 0) * (16 * ringUses 2 0 r + ind (r % 2 = 0) * gs) +
      ind (l = O.raw 1) * (16 * ringUses 2 1 r + ind (r % 2 = 1) * gs)
  | .rd => 64 * r + rd
  | _ => 0

/-- **The counts at a place**: prologue place `j`, block `r` at stage `i` after `rd` reads and
`gs` gathers, and the CTA barrier when `fin`. -/
def cntAt (j r i rd gs : Nat) (fin : Bool) (c : Cnt) : Nat :=
  proCnt O j c + loopCnt O r i rd gs c + if fin then ind (c = .bar 12) else 0
end

/-! ### The block loop -/

/-- The blocks the two lengths give (none for a total below 64). -/
def rounds (l0 l1 : BitVec 64) : Nat :=
  if scmpi .lt .s (tot l0 l1) 64 then 0 else (nblk l0 l1).toNat

/-- The loop registers are block `r`'s words. -/
def LoopOk (d : D) : Prop :=
  let R := rounds d.l0 d.l1
  let r := d.cnt.toNat
  scmpi .lt .s (tot d.l0 d.l1) 64 = false ∧ 1 ≤ R ∧ R < 2 ^ 26 ∧ r < R ∧ d.cnt = W r ∧
    d.buf = W (r % 2) ∧ d.slot = W (r % 4) ∧ d.pf = W (r / 2 % 2) ∧ d.pr = W (r / 4 % 2) ∧
    d.neg = W ((2 ^ 32 - R + r) % 2 ^ 32)

/-- A loop site. -/
def Site.inLoop : Site → Bool
  | .coordWait | .rawWait | .coord0 _ | .coord1 _ | .coord2 _ | .coord3 _ | .gather _
  | .rawArrive | .coordFree => true
  | _ => false

/-- The role's place facts and counts at a state, before undefined behaviour. -/
def RefCore (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Prop :=
  match d.site with
  | .exit =>
    (∀ c, c ≠ .ub → n c = cntAt (objs L g) 1 0 0 0 0 false c) ∨
      ∀ c, c ≠ .ub → n c = cntAt (objs L g) 3 (rounds d.l0 d.l1) 0 0 0 true c
  | .outBar => ∀ c, c ≠ .ub → n c = cntAt (objs L g) 3 (rounds d.l0 d.l1) 0 0 0 false c
  | s => if s.inLoop then
      LoopOk d ∧ ∀ c, c ≠ .ub → n c = cntAt (objs L g) 3 d.cnt.toNat s.stage s.rdN s.gN false c
    else ∀ c, c ≠ .ub → n c = cntAt (objs L g) s.pro 0 0 0 0 false c

/-- **The TMA warp's reference invariant**: before undefined behaviour, the place facts and
counts. -/
def Ref (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Prop := n .ub = 0 → RefCore L g d n

/-- **The sites' launch facts**: a length load's pointer is set, and the hand-back state is the
idle code's first event. -/
def SiteOk (P : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  (d.site = .loadTopk → eqz64 (pw8 (P.topkLenBase.getD 0)) = false) ∧
    (d.site = .loadExtra → eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false) ∧
    ∀ s, d.site = .leave s → s = idleFirst P L g

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
