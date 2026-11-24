-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxReads

@[expose] public section

/-! # The softmax warps as abstract states

The transitions of the softmax machine (`next`) and the invariant of a state (`Inv`). A load
may return any values: the state records the returned words (`loadW`), and the local run after
the implicit wait reads them. The machine continues when that run accepts them (`WaitOk`: the
packs, and after the last load the row maximum: no instruction faults) and the thread is dead
otherwise; likewise the exponentials after a tile's named barrier (`ExpOk0`, `ExpOk1`) and the
row sum after the statistics poll ending a tile (`StatsOk`). So the machine never gives up on a
thread. The values are those the code computes, which need not be numbers: the reference maximum
changes after the first tile's last load (to the value the `max.f32` tree computed, `rmax0V`, and
the words to the selected halves) and at the statistics poll ending a loop trip (to `mNV`), the
row sum at the second statistics poll of an item (`lsum0V`) and at the one ending a loop trip
(`lsum1V`): the code computes them in the segments that follow. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The role's first state. -/
def start : D := { site := .setMaxReg }

/-- After item `i`: the next item, or the tail. -/
def nextItem (L : Launch) (g : Nat) (d : D) : D :=
  if d.i + 1 < items L g then { d with site := .statsW 0, i := d.i + 1, t := 0 }
  else { d with site := .statsW 3, i := d.i + 1, t := 0 }

/-- After a successful statistics poll. -/
def afterStats (L : Launch) (d : D) : Fin 4 → D
  | 0 => { d with site := .sW false }
  | 1 => if trips L ≤ 1 then { d with site := .lSt, l := lsum0V L d }
    else { d with site := .sW true, l := lsum0V L d }
  | 2 =>
    let m' := mNV L d
    let l' := lsum1V L d
    if d.t + 2 < trips L then { d with site := .sW true, t := d.t + 1, m := m', l := l' }
    else { d with site := .lSt, t := d.t + 1, m := m', l := l' }
  | 3 => { d with site := .barEnd }

/-- The state after the implicit wait of load `c`. -/
def afterLoad (lp : Bool) (c : Fin 4) (d : D) : D :=
  match c with
  | 0 => { d with site := .ld lp 1 }
  | 1 => { d with site := .ld lp 2 }
  | 2 => { d with site := .ld lp 3 }
  | 3 => if lp then { d with site := .alphaSt }
    else { d with site := .gen 0, w := half d.w, m := rmax0V d.w }

open Classical in
/-- The abstract successor after event `e`. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .setMaxReg => some (some { d with site := .bar0 })
  | .bar0 =>
    if 0 < items L g then some (some { d with site := .statsW 0, i := 0, t := 0 })
    else some (some { d with site := .statsW 3, i := 0, t := 0 })
  | .statsW w => match e.kind with
    | .wait _ _ ok _ _ =>
      if ok then (if StatsOk L g w d then some (some (afterStats L d w)) else none)
      else some (some d)
    | _ => none
  | .sW lp => match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .ld lp 0 } else d))
    | _ => none
  | .ld lp c => match e.kind with
    | .tc (.ld _ vals .s32x32b) =>
      some (some { d with site := .ldW lp c, w := loadW d.w c.val vals })
    | _ => none
  | .ldW lp c => if WaitOk L g lp c d then some (some (afterLoad lp c d)) else none
  | .alphaSt => some (some { d with site := .gen 1 })
  | .gen 0 => if ExpOk0 L g d then some (some { d with site := .pst false 0 }) else none
  | .gen 1 => if ExpOk1 L g d then some (some { d with site := .pst true 0 }) else none
  | .gen 2 => some (some (nextItem L g d))
  | .pst lp 0 => some (some { d with site := .pst lp 1 })
  | .pst lp 1 => some (some { d with site := .pst lp 2 })
  | .pst lp 2 => some (some { d with site := .pwait lp 0 })
  | .pst lp 3 => some (some { d with site := .pwait lp 1 })
  | .pwait lp 0 => some (some { d with site := .pArr lp })
  | .pwait lp 1 => some (some { d with site := .warpBar lp })
  | .pArr lp => some (some { d with site := .pst lp 3 })
  | .warpBar lp => some (some { d with site := .el lp })
  | .el lp => match e.kind with
    | .elect _ _ ld =>
      if laneOf L g = ld then some (some { d with site := .p2Arr lp })
      else some (some { d with site := .statsW (if lp then 2 else 1) })
    | _ => none
  | .p2Arr lp => some (some { d with site := .statsW (if lp then 2 else 1) })
  | .lSt => some (some { d with site := .gen 2 })
  | .barEnd => some (some { d with site := .exit })
  | .exit => none

/-- **The machine never gives up**: every successor is a state, or none (the thread is dead or
the event is not the site's). -/
theorem next_ne (L : Launch) (g : Nat) (d : D) (e : Event) : next L g d e ≠ some none := by
  intro h
  unfold next at h
  repeat' split at h
  all_goals simp_all

/-! ### The invariant of a state -/

structure Inv (L : Launch) (g : Nat) (d : D) : Prop where
  /-- The thread is a softmax thread. -/
  warp : warpOf L g < 8
  /-- An item site is in an item of the cluster; the tail is after all of them. -/
  item : d.site.inItem = true → d.i < items L g
  tail : d.site = .statsW 3 ∨ d.site = .barEnd ∨ d.site = .exit → d.i = items L g ∧ d.t = 0
  start : d.site = .setMaxReg ∨ d.site = .bar0 → d.i = 0 ∧ d.t = 0
  /-- The first tile is at trip `0`, a loop trip is one of the `n - 1`, the end of an item is
  after them. -/
  tile0 : d.site.tile0 = true → d.t = 0
  trip : d.site.inTrip = true → d.t + 1 < trips L
  last : d.site = .lSt ∨ d.site = .gen 2 → d.t + 1 = trips L
  /-- The row sum has four bytes (the start's `b32 0`, or an outcome of `add.f32`), so its store
  at `lSt` writes it unchanged. -/
  lBytes : d.l.bytes = 4

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
