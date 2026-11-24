-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Next
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's blocks: where a state stands, and what a step keeps

The sites after the request's used-K read and before the scheduler's second pass are the tile's
blocks (`Site.blk`): the first block, the warm rounds, the steady rounds, and warp 14's last Bias
group after the warm rounds. A state's block (`bc`), the commits of its block before it
(`inBlk`) and the shuffles of its packet before it (`pktSh`) are functions of the site.

`blk_step`: a step from a block site other than the end of a block's V half and the end of the
last Bias group keeps the scan state, the tile's setup and the round counter, stays in the
block, and moves `inBlk` by the commit and `pktSh` by the shuffle it fires (a commit closes the
packet: its 32 shuffles become one commit of the block). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The tile's blocks: the first block, a warm round, a steady round, the last Bias group. -/
inductive Blk where
  | prime | warm | steady | tma6
  deriving DecidableEq

/-- The block of a site of the tile's loads (`none` elsewhere). -/
def bc : Site → Option Blk
  | .pgLd per _ | .pgSt per _ | .rwSt per _ | .slot per _ | .ptP per _ _ | .ptR per _ _
  | .ptS per _ _ | .lw per _ _ | .xl per _ _ | .xh per _ _ | .cp per _ _ _ | .commit per _
  | .arrive per _ =>
    some (match per with | .prime => .prime | .warm => .warm | .steady => .steady)
  | .tw t | .te t _ | .ta t | .tc t _ =>
    some (if t.val < 4 then .prime else if t.val < 6 then .warm else .tma6)
  | _ => none

/-- A site of the tile's loads. -/
abbrev Site.blk (s : Site) : Bool := (bc s).isSome

/-- The commits of the current block before a site. -/
def inBlk : Site → Nat
  | .slot _ v | .ptP _ v _ | .ptR _ v _ | .ptS _ v _ | .lw _ v _ | .xl _ v _ | .xh _ v _
  | .cp _ v _ _ | .commit _ v => if v then 1 else 0
  | .arrive _ v => if v then 2 else 1
  | .tw t | .te t _ | .ta t | .tc t _ => if t.val < 6 then 1 else 0
  | _ => 0

/-- The shuffles of the current packet before a site. -/
def pktSh : Site → Nat
  | .lw _ _ h => 16 * h.val
  | .xl _ _ i => 2 * i.val
  | .xh _ _ i => 2 * i.val + 1
  | .cp _ _ i _ => 2 * i.val + 2
  | .commit _ _ => 32
  | _ => 0

/-- A commit adds one to the block's commits. -/
def cm (e : Event) : Nat := match e.kind with | .asyncCommit => 1 | _ => 0

/-- The ends of a block's V half and of the last Bias group: their successors leave the block. -/
def Site.blkEnd : Site → Bool
  | .arrive _ v => v
  | .te t i => t.val = 6 ∧ i.val = 2
  | .tc t c => t.val = 6 ∧ c.val = 1
  | _ => false

variable {p : Params} {L : Launch} {g w : Nat}

theorem inBlk_arrive (per : Per) (v : Bool) :
    inBlk (.arrive per v) = inBlk (.commit per v) + 1 := by
  cases v <;> rfl

/-- A state at a page-table load holds the round's condition: its row is inside the used
length. -/
def RowOk (p : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  ∀ per it, d.site = .pgLd per it → rowCond p L g d.v per it = false

/-- The page loop's entry leads to a load only when the row is inside the used length. -/
theorem pgEnter_row (d : D) (per : Per) (it : Fin 2) : RowOk p L g (pgEnter p L g d per it) := by
  intro per' it' h
  unfold pgEnter D.iteS at h ⊢
  cases hc : rowCond p L g d.v per it <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · simp only [Site.pgLd.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hc
  · simp at h

/-- What a step inside a block keeps. -/
def BlkKeeps (p : Params) (L : Launch) (g : Nat) (d d' : D) (e : Event) : Prop :=
  d'.v.sc = d.v.sc ∧ d'.v.su = d.v.su ∧ d'.v.rnd = d.v.rnd ∧ bc d'.site = bc d.site ∧
    pktSh d'.site + 32 * cm e = pktSh d.site + Epilogue.sh e ∧ inBlk d'.site = inBlk d.site + cm e ∧
    Epilogue.vt e = 0 ∧ d'.v.ukw = d.v.ukw ∧ d'.v.r56 = d.v.r56 ∧ RowOk p L g d'

set_option maxHeartbeats 8000000 in
/-- **A step inside a block keeps the scan state, the setup and the round, and counts its commit
and its shuffle.** -/
theorem blk_step {d d' : D} {e : Event} (hb : d.site.blk = true) (hx : d.site.blkEnd = false)
    (hev : Ev p L g w d e) (hn : succ p L g w d e = some (some d')) : BlkKeeps p L g d d' e := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Site.blk, bc, Option.isSome, Bool.false_eq_true] at hb
  all_goals simp only [Ev] at hev
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals simp only [succ, word32, D.mk', pgEnter, D.iteS, pkStart, afterArrive, groupEnd,
    teNext, teElected, D.ite, reduceCtorEq] at hn
  all_goals (repeat' split at hn)
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals try subst hn
  all_goals try simp only [Site.blkEnd, decide_eq_false_iff_not] at hx

  all_goals try contradiction
  all_goals first
    | (simp [BlkKeeps, RowOk, bc, inBlk_arrive, pktSh, cm, Epilogue.sh, Epilogue.vt,
        Execution.isShfl, isFullVote, voteClass]; done)
    | (simp [BlkKeeps, RowOk, bc, inBlk, pktSh, cm, Epilogue.sh, Epilogue.vt, Execution.isShfl,
        isFullVote, voteClass]; done)
    | (simp [BlkKeeps, RowOk, bc, inBlk, pktSh, cm, Epilogue.sh, Epilogue.vt, Execution.isShfl,
        isFullVote, voteClass]; omega)
    | (simp [BlkKeeps, RowOk, bc, inBlk, pktSh, cm, Epilogue.sh, Epilogue.vt, Execution.isShfl,
        isFullVote, voteClass]; simp_all)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
