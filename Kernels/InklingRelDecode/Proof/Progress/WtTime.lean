-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Remaining
public import Kernels.InklingRelDecode.Proof.Bound.Base
public import Kernels.InklingRelDecode.Proof.Bound.DStart
public import Kernels.InklingRelDecode.Proof.Bound.ProA
public import Kernels.InklingRelDecode.Proof.Bound.Sm
public import Kernels.InklingRelDecode.Proof.Bound.Epi
public import Kernels.InklingRelDecode.Proof.Bound.Worker
public import Kernels.InklingRelDecode.Proof.Bound.Loader
public import Kernels.InklingRelDecode.Proof.Bound.Mma

@[expose] public section

/-!
# The virtual time of the abstract machine states

`Remaining.time` is a function of a thread and the abstract state of its machine alone. This file
defines it. The design (and why it has this shape) is in the development notes, "Progress layer: the
virtual time".

## The timeline

* **Fixed times before the loop.** The common start is at 2 to 24 (`dstartT`; the workers' first
  four sites are at the same times, so the two `bar.sync 0` of the common start of all eight warps
  are at 10 and 20). The prologue's sites are at `100 + ctorIdx` (`proT`), so its last site, the
  `barrier.sync 1` of the first generation, is at `c0`; the workers' dispatch loop head is at 30
  and its `barrier.sync 1` is at `c0` too (`workerT`). The second generation of barrier 1, which
  every role of the CTA enters, is at `c1 = c0 + 8`: the softmax region's `setmaxnreg` is at
  `c0 + 4` and its `barrier.sync 1` at `c1`, and so are the loader's, the MMA warp's and the idle
  role's.
* **The loop.** Slot `i` starts at `slot i = loop0 + span * i`. In it the loader's iteration `i`
  runs in the band `[0, 100)`, the MMA warp's iteration `i` (the QK half of block `i`, then the PV
  half of block `i - 1`) in `[100, 200)`, the softmax region's iteration `i` (block `i`) in
  `[200, 300)`. Within a band the time is the position of the site in its iteration (the `pos` of
  `Bound/*.lean`, which counts the sites left on the longest path).
* **After the loop.** Every loop time is below `epi0 - 100`. The MMA warp's three tail sites are at
  `epi0 - 100`, `- 96`, `- 92` (so before the epilogue's poll of `o_final` at `epi0`), and the
  epilogue's sites are at `epi0 + 4 * (75 - siteRank)`. The third generation of barrier 1 is at
  `c2 = epi0 + 276` (the epilogue's first `barrier.sync 1`, and the loader's, the MMA warp's and
  the idle role's last), the fourth at `c3 = epi0 + 288` (the epilogue's second, and the workers'
  dispatch loop head in its later round), and the last `bar.sync 0` of all threads at
  `c4 = epi0 + 292`.
* **Later rounds of the workers' loop.** The head of the loop (`setmaxnreg`, `barrier.sync 1`, the
  load of the role byte) in the later round (`Worker.late`) is at `c3 - 4`, `c3`, `c3 + 2`: after
  every role of the first round and before the exit.

All times are at least 2 (`time_ge_two`), which is `Remaining.wait_time`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000
open Classical

/-! ### Constants -/

/-- The width of a slot. -/
def span : Nat := 400
/-- The offsets of the bands within a slot: the loader, the MMA warp, the softmax region. -/
def bandL : Nat := 0
def bandM : Nat := 100
def bandS : Nat := 200
/-- The start of slot `0`: above every time before the loop. -/
def loop0 : Nat := 1000
/-- The start of slot `i`. -/
def slot (i : Nat) : Nat := loop0 + span * i
/-- The time of the prologue's last site, the first generation of barrier 1. -/
def c0 : Nat := 281
/-- The second generation of barrier 1. -/
def c1 : Nat := 289
/-- The epilogue's first site: above every slot a loop counter below `2 ^ 33` reaches. -/
def epi0 : Nat := loop0 + span * 8589934596
/-- The third generation of barrier 1. -/
def c2 : Nat := epi0 + 276
/-- The fourth generation of barrier 1. -/
def c3 : Nat := epi0 + 288
/-- The last generation of barrier 0, `bar.sync 0` of every thread. -/
def c4 : Nat := epi0 + 292

/-- `omega` with the constants of the timeline unfolded. -/
macro "wt_omega" : tactic =>
  `(tactic| (repeat (first
    | unfold c4 at *
    | unfold c3 at *
    | unfold c2 at *
    | unfold c1 at *
    | unfold c0 at *
    | unfold epi0 at *
    | unfold slot at *
    | unfold loop0 at *
    | unfold span at *
    | unfold bandL at *
    | unfold bandM at *
    | unfold bandS at *)) <;> omega)

/-! ### The machines' times -/

/-- The common start. -/
def dstartT (d : DStart.D) : Nat :=
  match d.site with
  | .alloc => 2 | .allocWr => 4 | .bar0 => 10 | .ld0 => 12 | .bar1 => 20 | .relinq => 22
  | .shfl => 24 | .toProA => 26

/-- The prologue: its position in the code. -/
def proT (d : ProA.D) : Nat := 100 + d.site.ctorIdx

/-- The softmax region: the setup sites before the loop at `c0 + 4`, `c1` and `c1 + 4 + 4 j`, the
loop's sites at their slot's band `bandS` and their position in the iteration. -/
def smT (d : Sm.D) : Nat :=
  match d.site with
  | .setMaxReg => c0 + 4
  | .bar0 => c1
  | .pre j => c1 + 4 + 4 * j.val
  | s => slot d.i + bandS + (90 - Bound.Sm.pos s)

/-- The epilogue: four per site after the loop. -/
def epiT (d : Epi.D) : Nat := epi0 + 4 * (75 - Bound.Epi.siteRank d.site)

/-- The default-partition thread. -/
def dcompT : DComp.St → Nat
  | .dstart d => dstartT d
  | .pro d => proT d
  | .sm d => smT d
  | .epi d => epiT d

/-- The worker's own sites. The later round of the dispatch loop is marked in the inherited
registers (`Worker.late`). -/
def workerT (d : Worker.D) : Nat :=
  match d.site with
  | .bar0 => 10 | .ld0 => 12 | .bar1 => 20 | .shfl => 24
  | .loop => if Worker.late d.P then c3 - 4 else 30
  | .bar2 => if Worker.late d.P then c3 else c0
  | .ldRole => if Worker.late d.P then c3 + 2 else c0 + 2
  | .bad0 => if Worker.late d.P then c3 + 3 else c0 + 3
  | .bad1 => if Worker.late d.P then c3 + 4 else c0 + 4
  | .toIdle | .toLoader | .toMma | .toExit => 2

/-- The idle role. -/
def idleT (d : Worker.Idle.D) : Nat :=
  match d.site with
  | .dec => c0 + 4 | .bar0 => c1 | .bar1 => c2 | .inc => c2 + 4

/-- The loader: the sites before and after the loop at fixed times, the loop's at their slot's
band `bandL`. -/
def loaderT (d : Loader.D) : Nat :=
  match d.site with
  | .setMaxDec => c0 + 4 | .ld0 => c0 + 6 | .ld1 => c0 + 7 | .bar0 => c1
  | .bar1 => c2 | .setMaxInc => c2 + 4
  | s => slot d.i + bandL + (21 - Bound.Loader.pos s)

/-- The MMA warp: the loop's sites at their slot's band `bandM`, the three tail sites before the
epilogue. -/
def mmaT (d : Mma.D) : Nat :=
  match d.site with
  | .setMaxReg => c0 + 4 | .ldNum => c0 + 6 | .bar0 => c1
  | .finBar => epi0 - 100 | .finElect => epi0 - 96 | .finCommit => epi0 - 92
  | .bar1 => c2 | .setMaxRegInc => c2 + 4
  | s => slot d.i + bandM + (28 - Bound.Mma.pos s)

/-- The exit role. -/
def exitT (x : WComp.ExitD) : Nat :=
  match x.site with
  | .bar => c4
  | .ret => c4 + 2

/-- The worker thread. -/
def wcompT : WComp.WSt → Nat
  | .worker d => workerT d
  | .idle d => idleT d
  | .loader d _ => loaderT d
  | .mma d _ => mmaT d
  | .exit x => exitT x

/-- **The virtual time** of the abstract state `d` of thread `g`'s machine. -/
def time (_g : Nat) : TSt → Nat
  | .d s => dcompT s
  | .w s => wcompT s

/-! ### Every time is at least 2 -/

theorem dstartT_ge (d : DStart.D) : 2 ≤ dstartT d := by
  obtain ⟨s, tm⟩ := d
  cases s <;> simp [dstartT]

theorem workerT_ge (d : Worker.D) : 2 ≤ workerT d := by
  obtain ⟨s, P⟩ := d
  cases s <;> simp only [workerT] <;> (try split_ifs) <;> wt_omega

theorem smT_ge (d : Sm.D) : 2 ≤ smT d := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [smT] <;> wt_omega

theorem loaderT_ge (d : Loader.D) : 2 ≤ loaderT d := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> simp only [loaderT] <;> wt_omega

theorem mmaT_ge (d : Mma.D) : 2 ≤ mmaT d := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp only [mmaT] <;> wt_omega

/-- **Every state's time is at least 2.** In particular the states at an mbarrier poll are
(`Remaining.wait_time`). -/
theorem time_ge_two (g : Nat) (d : TSt) : 2 ≤ time g d := by
  cases d with
  | d s =>
    cases s with
    | dstart d => exact dstartT_ge d
    | pro d => simp only [time, dcompT, proT]; omega
    | sm d => exact smT_ge d
    | epi d => simp only [time, dcompT, epiT]; wt_omega
  | w s =>
    cases s with
    | worker d => exact workerT_ge d
    | idle d =>
      obtain ⟨s, P⟩ := d
      cases s <;> simp only [time, wcompT, idleT] <;> wt_omega
    | loader d P => exact loaderT_ge d
    | mma d P => exact mmaT_ge d
    | exit x =>
      obtain ⟨s, P⟩ := x
      cases s <;> simp only [time, wcompT, exitT] <;> wt_omega

/-- **`Remaining.wait_time`**: a state at an mbarrier poll is timed at least 2. -/
theorem wait_time (g : Nat) (d : TSt) (_ : nextKind d = .wait) : 2 ≤ time g d :=
  time_ge_two g d

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
