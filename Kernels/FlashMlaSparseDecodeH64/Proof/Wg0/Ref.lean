-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Cnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Flow.Arith32Norm

@[expose] public section

/-! # Warpgroup 0's reference invariant

The role's mbarrier events follow one fixed order: the arrival on the last-store barrier (pc 200),
then per block `r` the successful poll of the valid-mask slot `r % 4` (264), the successful poll
of the QK slot `r % 2` (272), the arrival freeing the valid-mask slot `r % 4` (571) and the
arrival on the softmax-ready slot `r % 2` (1122); after the `R` blocks the successful poll of the
SV slot `(R - 1) % 2` (1184). Every CTA is inside the batch (`batch_in`, `Lib/Rounds.lean`): no
lane ends at the sink.

The ledger's counts of the mbarrier classes (`Cnt.acq l`, `Cnt.arrive l`) at a state are the
counts of that order up to the state's place (`Counts`): its region (`Site.reg`: set-up, block
loop, epilogue, end) and its place in a block or in the epilogue (`Site.idx`). Every object is a
parameter (`Objs`): the counts are sums of indicators `ind (l = O.x j)` times uses of a ring slot
(`ringUses`), so a step on one object never compares two concrete locations.

In the block loop the state's words are block `r`'s (`LoopOk`): the block number `bi = r + 1`, the
negative counter `cnt = r + 1 - R` modulo `2 ^ 32` (`R`: the blocks the two lengths give,
`rounds`), the valid-mask ring's slot `r % 4` and parity `r / 4 % 2`, the score ring's slot
`r % 2` and parity `r / 2 % 2`. In the epilogue the score ring's words are those of the last block
(`EpiOk`). The launch facts (`LaunchOk`): a length load's pointer is set, and the length words
loaded are the launch's (`lenWA`, `lenWB`), so the block count is the CTA's `blocksOf`. The
vote's result (`vt`) only selects the rescale arm, whose events are in no class `Ref` states.
Before undefined behaviour (the class `ub`) the counts are those of the state's
place (`Ref`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-! ### The objects -/

/-- A ring slot's word: the shared base plus eight bytes per slot `v`, plus `c`. -/
abbrev slotW (L : Launch) (v : BitVec 64) (c : Int) : BitVec 64 := addi (add32 (sbw L) (shl v 3)) c

section
variable (L : Launch) (g : Nat)

@[irreducible] def lastL : Loc := smLoc L g (arrW L) 0
@[irreducible] def vReadyL (j : Nat) : Loc := smLoc L g (slotW L (W j) 222840) 0
@[irreducible] def vFreeL (j : Nat) : Loc := smLoc L g (slotW L (W j) 222872) 0
@[irreducible] def qkL (j : Nat) : Loc := smLoc L g (slotW L (W j) 222904) 0
@[irreducible] def soL (j : Nat) : Loc := smLoc L g (slotW L (W j) 222920) 0
@[irreducible] def svL (j : Nat) : Loc := smLoc L g (slotW L (W j) 222936) 0
end

/-- The role's objects as parameters of the counts. -/
structure Objs where
  last : Loc
  vReady : Nat → Loc
  vFree : Nat → Loc
  qk : Nat → Loc
  so : Nat → Loc
  sv : Nat → Loc

/-- The launch's objects. -/
def objs (L : Launch) (g : Nat) : Objs :=
  ⟨lastL L g, vReadyL L g, vFreeL L g, qkL L g, soL L g, svL L g⟩

/-! ### The counts -/

/-- `1` when `p` holds. -/
abbrev ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- The uses of slot `j` of an `S`-slot ring before block `r` at place `i`, the block's use being
at place `k`. -/
def use (S j r i k : Nat) : Nat := ringUses S j r + ind (r % S = j ∧ k ≤ i)

section
variable (O : Objs)

/-- The successful polls of `l` before place `i` of block `r` (`sv`: the SV slot polled). -/
def acqCnt (r i : Nat) (sv : Option Nat) (l : Loc) : Nat :=
  ind (l = O.vReady 0) * use 4 0 r i 1 + ind (l = O.vReady 1) * use 4 1 r i 1 +
    ind (l = O.vReady 2) * use 4 2 r i 1 + ind (l = O.vReady 3) * use 4 3 r i 1 +
    ind (l = O.qk 0) * use 2 0 r i 2 + ind (l = O.qk 1) * use 2 1 r i 2 +
    match sv with | some j => ind (l = O.sv j) | none => 0

/-- The arrivals on `l` before place `i` of block `r` (`a`: after the last-store arrival). -/
def arrCnt (a : Bool) (r i : Nat) (l : Loc) : Nat :=
  (if a then ind (l = O.last) else 0) +
    ind (l = O.vFree 0) * use 4 0 r i 3 + ind (l = O.vFree 1) * use 4 1 r i 3 +
    ind (l = O.vFree 2) * use 4 2 r i 3 + ind (l = O.vFree 3) * use 4 3 r i 3 +
    ind (l = O.so 0) * ringUses 2 0 r + ind (l = O.so 1) * ringUses 2 1 r

/-- **The counts at a place.** -/
def Counts (n : Cnt → Nat) (a : Bool) (r i : Nat) (sv : Option Nat) : Prop :=
  (∀ l, n (.acq l) = acqCnt O r i sv l) ∧ ∀ l, n (.arrive l) = arrCnt O a r i l
end

/-! ### Places -/

/-- The regions of the role. -/
inductive Reg where
  | setup | loop | epi | fin
  deriving DecidableEq

/-- The region of a site. -/
def Site.reg : Site → Reg
  | .smr | .sink | .lenA | .lenB | .bwait | .arrL => .setup
  | .ebar0 | .est | .ebar1 | .eld | .lse | .wsv | .efa | .old _ | .oldw _ | .ost2 _ _ | .ofpx _
  | .obar _ | .oel _ | .otma _ | .commit | .ebar => .epi
  | .dealloc | .exit => .fin
  | _ => .loop

/-- The place of a site in a block (the block's mbarrier events before it), or in the epilogue
(after the SV poll). -/
def Site.idx : Site → Nat
  | .wq => 1
  | .tcfa | .sld _ _ | .sldw | .tcfb | .vm | .pst _ | .bar1 | .pld _ | .mst | .bar2 | .arrV => 2
  | .mld | .vote | .ost _ | .rsf | .rld _ | .rldw _ | .rst _ | .rstw _ | .rsfb | .fpx
  | .arrS => 3
  | .efa | .old _ | .oldw _ | .ost2 _ _ | .ofpx _ | .obar _ | .oel _ | .otma _ | .commit
  | .ebar => 1
  | _ => 0

/-- The words of a state that the invariant reads. -/
structure Words where
  l0 : BitVec 64
  l1 : BitVec 64
  cnt : BitVec 64
  bi : BitVec 64
  vs : BitVec 64
  pv : BitVec 64
  sl : BitVec 64
  ps : BitVec 64

def Control.D.words (d : D) : Words := ⟨d.l0, d.l1, d.cnt, d.bi, d.vs, d.pv, d.sl, d.ps⟩

/-- The blocks the two lengths give (none for a padded total below 64). -/
def rounds (l0 l1 : BitVec 64) : Nat :=
  if scmpi .lt .s (r15 l0 l1) 64 then 0 else (nblk l0 l1).toNat

/-- The words are block `r`'s. -/
def LoopOk (w : Words) (r : Nat) : Prop :=
  scmpi .lt .s (r15 w.l0 w.l1) 64 = false ∧ rounds w.l0 w.l1 < 2 ^ 26 ∧
    r < rounds w.l0 w.l1 ∧ w.bi = W (r + 1) ∧
    w.cnt = W ((2 ^ 32 + 1 + r - rounds w.l0 w.l1) % 2 ^ 32) ∧
    w.vs = W (r % 4) ∧ w.pv = W (r / 4 % 2) ∧ w.sl = W (r % 2) ∧ w.ps = W (r / 2 % 2)

/-- The score ring's words are the last block's. -/
def EpiOk (w : Words) : Prop :=
  w.sl = W ((rounds w.l0 w.l1 - 1) % 2) ∧ w.ps = W ((rounds w.l0 w.l1 - 1) / 2 % 2)

/-- The SV slot the epilogue polls. -/
def svSlot (w : Words) : Nat := (rounds w.l0 w.l1 - 1) % 2

/-- The place facts and counts of region `k`, place `i`, words `w`. -/
def RefAt (O : Objs) (k : Reg) (i : Nat) (w : Words) (n : Cnt → Nat) : Prop :=
  match k with
  | .setup => Counts O n false 0 0 none
  | .loop => ∃ r, LoopOk w r ∧ Counts O n true r i none
  | .epi => EpiOk w ∧
      Counts O n true (rounds w.l0 w.l1) 0 (if i = 1 then some (svSlot w) else none)
  | .fin => EpiOk w ∧ Counts O n true (rounds w.l0 w.l1) 0 (some (svSlot w))

/-- The role's place facts and counts at a state, before undefined behaviour. -/
def RefCore (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Prop :=
  RefAt (objs L g) d.site.reg d.site.idx d.words n

/-- How many of the two length words a site has loaded: none up to the first length load, the
first at the second length load, both after. -/
def Site.lens : Site → Nat
  | .smr | .sink | .lenA => 0
  | .lenB => 1
  | _ => 2

/-- **The launch facts of a state**: at a length load the length's pointer is set, and the length
words loaded are the launch's (`lenWA`, `lenWB` of the lane's CTA, `Lib/Rounds.lean`). -/
def LaunchOk (P : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  (d.site = .lenA → eqz64 (pw8 (P.topkLenBase.getD 0)) = false) ∧
    (d.site = .lenB → eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false) ∧
    (1 ≤ d.site.lens → d.l0 = lenWA P L (g / L.block)) ∧
    (2 ≤ d.site.lens → d.l1 = lenWB P L (g / L.block))

/-! ### Barrier ordinals -/

/-- The sites of the barrier events: barrier 9 (`bar0`, `bar2`, `ebar0`, `ebar1`, `obar c`), the
warp pair's barrier (`bar1`), barrier 12 (`ebar`). -/
def Site.isBar : Site → Bool
  | .bar0 | .bar1 | .bar2 | .ebar0 | .ebar1 | .obar _ | .ebar => true
  | _ => false

/-- The barrier events of a site's block (or of the epilogue) before it. -/
def Site.bidx : Site → Nat
  | .wv | .wq | .tcfa | .sld _ _ | .sldw | .tcfb | .vm | .pst _ | .bar1 => 1
  | .pld _ | .mst | .bar2 => 2
  | .arrV | .mld | .vote | .ost _ | .rsf | .rld _ | .rldw _ | .rst _ | .rstw _ | .rsfb | .fpx
  | .arrS => 3
  | .est | .ebar1 => 1
  | .eld | .lse | .wsv | .efa => 2
  | .old c | .oldw c | .ost2 c _ | .ofpx c | .obar c => 2 + c.val
  | .oel c | .otma c => 3 + c.val
  | .commit | .ebar => 6
  | .dealloc | .exit => 7
  | _ => 0

/-- **The barrier ordinal of a state**: the role's barrier events before it, three per block
(block `bi - 1`), then seven in the epilogue and the end after the `R` blocks. -/
def barOrd (d : D) : Nat :=
  (match d.site.reg with
    | .setup => 0
    | .loop => 3 * (d.bi.toNat - 1)
    | _ => 3 * rounds d.l0 d.l1) + d.site.bidx

/-- The role's barrier events counted by the ledger. -/
def barTot (n : Cnt → Nat) : Nat := n (.bar 9) + n (.bar 10) + n (.bar 11) + n (.bar 12)

/-- **The barrier facts of a state**: the role's barrier events are on barriers 9 to 12, as many
as the state's ordinal. -/
def BarOk (d : D) (n : Cnt → Nat) : Prop :=
  (∀ id, id ≠ 9 → id ≠ 10 → id ≠ 11 → id ≠ 12 → n (.bar id) = 0) ∧ barTot n = barOrd d

/-- **Warpgroup 0's reference invariant**: before undefined behaviour, the place facts and
counts, the launch facts and the barrier facts. -/
def Ref (P : Params) (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) : Prop :=
  n .ub = 0 → RefCore L g d n ∧ LaunchOk P L g d ∧ BarOk d n

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
