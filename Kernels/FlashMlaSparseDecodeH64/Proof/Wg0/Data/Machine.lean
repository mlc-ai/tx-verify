-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataFacts
public import Lemmas.Flow.DataOver

@[expose] public section

/-! # Warpgroup 0 as a data machine (the block loop's reads)

The control machine (`Control.code`) with the values the block loop reads, recorded as the
events deliver them (the words the payloads rebuild to, "reads as"):

* the block's score words: the two Tensor Memory loads `sld a k` give the 32 words of the low
  half (`%r2428`–`%r2459`, `lo`) and of the high half (`%r2460`–`%r2491`, `hi`); which load is
  which depends on the arm (`sldLo`);
* the valid-mask word (`vm`, `mw`), the sixteen peer elements (`pld k`, two per site, `pw`) and
  the peer's row maximum (`mld`, `pm`);
* the words of the current rescale chunk (`rld c`, `o`);
* at the softmax-ready arrival (`arrS`) the block's reads move to the history (`hist`, oldest
  first) and the block fields are cleared.

A step is the control step; the data never stops the machine, so it lies over the control
machine (`over`) by construction. **The data facts** (`dF`) of a state are the facts of its site
from the block's reads (`wF`, generated: `Gen/DataFacts.lean`, `Gen/w0site_gen.py`), while the
state is on the block's chain of sites (`ok`): from the first score load on, every step goes to the
site the code goes to next (`succOk`); another successor leaves the chain and has no data facts.
The chain starts at the `setmaxnreg` (`smr`): the set-up sites hold the scale word (`%r9`, the
`ld.param` at pc 146: `scX`), the loop's head (from `bar0`) also its duplicated pair (`%rd254`)
and the statistics the block starts from (`Blk.m`, `l`, `mx`; the arrival `arrL` records their
initial values, the moves at pcs 247–249). So far the chain covers the set-up, the loop head and
the sink word (`%r2422`, `Blk.sk`: `-inf` from the start-up as a control fact up to pc 156, the
scaled sink load after the `sink` event, carried by every link) and
the block's data sites from the score loads to the last peer load (the peer exchange: masked
scores, packed stores, peer sums); the later sites and the epilogue have no data facts yet. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A state: the control state, the current block's reads and the finished blocks' reads. -/
structure D where
  c : Control.D
  b : Blk := {}
  hist : List Blk := []
  ok : Bool := false

/-- The scale's bits, as the `ld.param` at pc 146 loads them into `%r9`. -/
def scX (L : Launch) : BitVec 64 := BitVec.ofNat 64 (leNat (scaleBits L) 0 4)

/-- The statistics' initial words (pcs 247–249): `m` is `-1e30` (`0fF149F2CA`), `l` is `0`, `mx`
is `-inf` (`0fFF800000`). -/
def mI : Value := w32 (BitVec.ofNat 64 4048155338)
def lI : Value := w32 (BitVec.ofNat 64 0)
def mxI : Value := w32 (BitVec.ofNat 64 4286578688)

/-- The value a load's bytes rebuild to (as the control machine reads it). -/
def loadVal (bs : List (Option Byte)) : Value := (rebuild 3 bs).toOption.getD (.pred false)

/-- Whether score load `k` of arm `a` writes the low half (`%r2428`–`%r2459`): the second load of
the first arm (pc 280) and the first of the second (pc 283). -/
def sldLo (a : Bool) (k : Fin 2) : Bool := a == (k.val == 0)

/-- The block's reads after the event `e` at control state `c`. -/
def record (c : Control.D) (e : Event) (b : Blk) : Blk :=
  match c.site, e.kind with
  | .sld a k, .tc (.ld _ vals _) =>
    if sldLo a k then { b with lo := vals } else { b with hi := vals }
  | .vm, .rd _ bs => { b with mw := loadVal bs }
  | .pld k, .rd _ bs =>
    if c.el = 0 then b
    else { b with pw := fun j => if j = k.val then (c.a0, loadVal bs) else b.pw j }
  | .mld, .rd _ bs => { b with pm := loadVal bs }
  | .vote, .voteMode _ _ _ r => { b with vt := r }
  | .rld _, .tc (.ld _ vals _) => { b with o := vals }
  | .arrL, _ => { b with m := mI, l := lI, mx := mxI }
  | .smr, _ => { b with sk := mxI }
  | .sink, .nc _ bs => { b with sk := Gen.sk_v157 fun _ => loadVal bs }
  | .eld, .rd _ bs => { b with pe := loadVal bs }
  | .old _, .tc (.ld _ vals _) => { b with o := vals }
  | _, _ => b

/-- The first site of the chain (the `setmaxnreg`). -/
def isStart : Site → Bool
  | .smr => true
  | _ => false

/-- Whether the step from `c` to `c'` stays on the block's chain of sites. -/
def succOk (c c' : Control.D) : Bool :=
  match c.site with
  | .smr => decide (c'.site ∈ [.sink, .lenA, .lenB, .bwait])
  | .sink => decide (c'.site ∈ [.lenA, .lenB, .bwait])
  | .lenA => decide (c'.site ∈ [.lenB, .bwait])
  | .lenB => decide (c'.site = .bwait)
  | .bwait => decide (c'.site = .arrL)
  | .arrL => decide (c'.site = .bar0 ∨ c'.site = .ebar0)
  | .bar0 => decide (c'.site = .wv)
  | .wv => decide (c'.site ∈ [.wv, .wq])
  | .wq => decide (c'.site ∈ [.wq, .tcfa])
  | .tcfa => decide (c'.site ∈ [.sld false 0, .sld true 0])
  | .sld a 0 => decide (c'.site = .sld a 1)
  | .sld _ _ => decide (c'.site = .sldw)
  | .sldw => decide (c'.site = .tcfb)
  | .tcfb => decide (c'.site = .vm)
  | .vm => decide (c'.site = .pst 0)
  | .pst k =>
    decide (c'.site = [.pst 1, .pst 2, .pst 3, .pst 4, .pst 5, .pst 6, .pst 7].getD k.val .bar1)
  | .bar1 => decide (c'.site = .pld 0)
  | .pld k =>
    if c.el = 0 then decide (c'.site = .pld k)
    else decide (c'.site = [.pld 1, .pld 2, .pld 3, .pld 4, .pld 5, .pld 6, .pld 7].getD k.val .mst)
  | .mst => decide (c'.site = .bar2)
  | .bar2 => decide (c'.site = .arrV)
  | .arrV => decide (c'.site = .mld)
  | .mld => decide (c'.site = .vote)
  | .vote => decide (c'.site = .ost 0)
  | .ost k =>
    if c.el + 1 < 4 then decide (c'.site = .ost k)
    else if k.val < 3 then decide (c'.site = [.ost 1, .ost 2, .ost 3].getD k.val .vote)
    else decide (c'.site ∈ [.rsf, .fpx])
  | .rsf => decide (c'.site = .rld 0)
  | .rld k => decide (c'.site = .rldw k)
  | .rldw k => decide (c'.site = .rst k)
  | .rst k => decide (c'.site = .rstw k)
  | .rstw k => decide (c'.site = [.rld 1, .rld 2, .rld 3].getD k.val .rsfb)
  | .rsfb => decide (c'.site = .fpx)
  | .fpx => decide (c'.site = .arrS)
  | .ebar0 => decide (c'.site = .est)
  | .est => decide (c'.site = .ebar1)
  | .ebar1 => decide (c'.site = .eld)
  | .eld => decide (c'.site ∈ [.lse, .wsv])
  | .lse => decide (c'.site = .wsv)
  | .wsv => decide (c'.site ∈ [.wsv, .efa])
  | .efa => decide (c'.site = .old 0)
  | .old k => decide (c'.site = .oldw k)
  | .oldw k => decide (c'.site = .ost2 k 0)
  | .ost2 k j =>
    if c.el + 1 < 4 then decide (c'.site = .ost2 k j)
    else decide (c'.site = [.ost2 k 1, .ost2 k 2, .ost2 k 3, .ost2 k 4, .ost2 k 5, .ost2 k 6,
      .ost2 k 7].getD j.val (.ofpx k))
  | .ofpx k => decide (c'.site = .obar k)
  | .obar k => decide (c'.site = .oel k ∨ c'.site ∈ [.old 1, .old 2, .old 3])
  | .oel k => decide (c'.site = .otma k ∨ c'.site ∈ [.old 1, .old 2, .old 3])
  | .otma _ => decide (c'.site ∈ [.old 1, .old 2, .old 3])
  | _ => false

/-- The data after the control step to `c'` on event `e`. -/
def dataNext (L : Launch) (d : D) (c' : Control.D) (e : Event) : D :=
  match d.c.site with
  | .arrS =>
    let V := lookupD (wF (scX L) .arrS d.b)
    { c := c', b := { m := V 2950, l := V 2955, mx := V 2885, sk := V 2880 },
      hist := d.hist ++ [d.b], ok := d.ok }
  | _ => { c := c', b := record d.c e d.b, hist := d.hist,
           ok := (isStart d.c.site || d.ok) && succOk d.c c' }

theorem dataNext_c (L : Launch) (d : D) (c' : Control.D) (e : Event) :
    (dataNext L d c' e).c = c' := by
  unfold dataNext
  split <;> rfl

/-- **The successor**: the control successor, with the data. -/
def succ (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D) (e : Event) :
    Option (Option D) :=
  (Control.succ P L g w d.c e).map (Option.map fun c' => dataNext L d c' e)

/-- **The data facts** of a state: its site's facts while it is on the block's chain. -/
def dF (L : Launch) (d : D) : List (Nat × Value) := if d.ok then wF (scX L) d.c.site d.b else []

/-- **Warpgroup 0 as a data machine** (for the warp word `w`). -/
@[reducible] def code (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := { c := (Control.code P L g w).init }
  pc := fun d => (Control.code P L g w).pc d.c
  facts := fun d => (Control.code P L g w).facts d.c ++ dF L d
  sub := fun d => (Control.code P L g w).sub d.c
  acc := fun d => (Control.code P L g w).acc d.c
  inv := fun d => (Control.code P L g w).inv d.c
  next := succ P L g w

/-- **The data machine lies over the control machine.** -/
theorem over (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code.Over (code P L g w) (Control.code P L g w) D.c (dF L) where
  pc _ := rfl
  sub _ := rfl
  acc _ := rfl
  inv _ := Iff.rfl
  facts _ := rfl
  next := by
    intro d e d' h
    change (Control.succ P L g w d.c e).map _ = _ at h
    cases hc : Control.succ P L g w d.c e with
    | none => rw [hc] at h; cases h
    | some o =>
      rw [hc] at h
      cases o with
      | none => cases h
      | some c' =>
        cases h
        change _ = some (some (dataNext L d c' e).c)
        rw [dataNext_c]
        exact hc
  stop := by
    intro d e h
    change (Control.succ P L g w d.c e).map _ = _ at h
    cases hc : Control.succ P L g w d.c e with
    | none => exact hc
    | some o => rw [hc] at h; cases h

theorem erases (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) :
    Code.Erases (code P L g w) (Control.code P L g w) D.c :=
  (over P L g w).erases rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
