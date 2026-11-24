-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WqKxD

@[expose] public section

/-!
# The time of a key: the worker warps

The key of a worker state (`wKey`) is the position of its next synchronizing state only; the
time of that state (`Wt.time`) also depends on the loop counter (the loader, the MMA warp) and on
the round marker of the dispatch loop (`Worker.late`). `kxW` is the time of the next
synchronizing state, read off the state's own fields: the state's own time at a synchronizing
state, and at a silent one the time of the synchronizing state its stretch ends at (the loader's
copies of the last block end at the next iteration's first warp barrier or at `bar1`, the MMA
warp's MMAs at the site the half's successor gives).

* `kxW_sy`: a synchronizing state's key time is its time.
* `kxW_lt`: a silent state (with its invariant) is timed below its key time.

`kxW_silent` (a silent step keeps the key time) is in `WqKxWStep.lean`, `kxW_step` (two lanes'
synchronizing states of one key and one key time, which agree, `WAgree`, and satisfy `WValid`:
the loader's counter at `bar0` and the MMA warp's at its `bar0` are the same for both, the
dispatch's first round is not marked late; their successors have one key time) in
`WqKxWComp.lean`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

/-! ### The key times -/

/-- The worker's own states: the load of the base word ends at `bar1`. -/
def kxWk (d : Worker.D) : Nat :=
  match d.site with
  | .ld0 => 20
  | _ => workerT d

/-- The loader. -/
def kxL (d : Loader.D) : Nat :=
  match d.site with
  | .ld0 | .ld1 => c1
  | .wait => loaderT { d with site := .wb0 }
  | .arrive | .ldb0 => loaderT { d with site := .wb1 }
  | .cp0a | .cp0b => loaderT { d with site := .wb2 }
  | .cp1a | .cp1b | .ldb1 => loaderT { d with site := .wb3 }
  | .cp2a | .cp2b => loaderT { d with site := .wb4 }
  | .cp3a | .cp3b =>
    if d.n = (d.i + 1) % 2 ^ 32 then c2
    else loaderT { d with site := .wb0, i := d.i + 1 }
  | _ => loaderT d

/-- The MMA warp. -/
def kxM (d : Mma.D) : Nat :=
  match d.site with
  | .ldNum => c1
  | .kvWait => mmaT { d with site := .qkShfl }
  | .pWait => mmaT { d with site := .pvShfl }
  | .qk _ | .qkCommit => mmaT (Mma.afterQk d)
  | .pv _ | .pvCommit1 | .pvCommit2 => mmaT (Mma.iterNext d)
  | .finCommit => c2
  | _ => mmaT d

/-- The exit role: `ret` ends the thread. -/
def kxX (x : WComp.ExitD) : Nat :=
  match x.site with
  | .bar => c4
  | .ret => c4 + 3

/-- **The key time of a worker state.** -/
def kxW : WComp.WSt → Nat
  | .worker d => kxWk d
  | .idle d => idleT d
  | .loader d _ => kxL d
  | .mma d _ => kxM d
  | .exit x => kxX x

/-- What two lanes' synchronizing states must satisfy beyond the key for their successors to
have one key time: the loader's and the MMA warp's counters at `bar0` are `c` and `0`, the
dispatch's first shuffle is not marked late. -/
def WValid (c : Nat) : WComp.WSt → Prop
  | .worker w => w.site = .shfl → ¬ Worker.late w.P
  | .loader d _ => d.site = .bar0 → d.i = c
  | .mma d _ => d.site = .bar0 → d.i = 0
  | _ => True

/-! ### Synchronizing states -/

theorem kxW_sy {s : WComp.WSt} (h : wSy s = true) : kxW s = wcompT s := by
  cases s with
  | worker d =>
    obtain ⟨site, P⟩ := d
    cases site <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at h <;>
      first | rfl | (exfalso; revert h; decide +kernel)
  | idle d => rfl
  | loader d P =>
    obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
    cases site <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Loader.sub,
      Bool.or_false] at h <;>
      first | rfl | (exfalso; revert h; decide +kernel)
  | mma d P =>
    obtain ⟨site, i, n, tm, pro⟩ := d
    cases site <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at h <;>
      first | rfl | (exfalso; revert h; decide +kernel) |
        (exfalso; rename_i j; revert h j; decide +kernel)
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at h <;>
      first | rfl | (exfalso; revert h; decide +kernel)

/-! ### Silent states are timed below their key time -/

theorem kxWk_lt {d : Worker.D} (h : wSy (.worker d) = false) : workerT d < kxWk d := by
  obtain ⟨site, P⟩ := d
  cases site <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at h <;>
    first | (exfalso; revert h; decide +kernel) | (simp only [kxWk, workerT]; omega)

theorem kxL_lt {L : Launch} {g : Nat} {d : Loader.D} {P : Loader.Pro}
    (h : wSy (.loader d P) = false) (hI : Loader.Inv L g d) : loaderT d < kxL d := by
  have hb : d.site.inLoop = true → d.i < 2 ^ 33 := fun hl => by
    have h1 := (hI.loop hl).2
    have h2 := Raw.word32Of_lt (hI.bits hl).2
    omega
  obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
  cases site <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Loader.sub,
      Bool.or_false] at h <;>
    first
    | (exfalso; revert h; decide +kernel)
    | (simp only [Loader.Site.inLoop, forall_const] at hb
       simp only [kxL, loaderT, Bound.Loader.pos]
       (try split) <;> wt_omega)

theorem mmaT_iterNext (d : Mma.D) : mmaT (Mma.iterNext d) =
    if d.i = d.n then epi0 - 100 else if d.i + 1 < d.n then slot (d.i + 1) + bandM + 0
    else slot (d.i + 1) + bandM + 14 := by
  unfold Mma.iterNext
  split_ifs <;> rfl

theorem mmaT_afterQk (d : Mma.D) : mmaT (Mma.afterQk d) =
    if d.i = 0 then mmaT (Mma.iterNext d) else slot d.i + bandM + 14 := by
  unfold Mma.afterQk
  split_ifs <;> rfl

theorem kxM_lt {d : Mma.D} {P : Loader.Pro} (h : wSy (.mma d P) = false) (hI : Mma.Inv d) :
    mmaT d < kxM d := by
  have hq := hI.qk
  have hp := hI.pv
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at h <;>
    first
    | (exfalso; revert h; decide +kernel)
    | (simp only [Mma.QkSite, Mma.PvSite, forall_const] at hq hp
       simp only [kxM, mmaT_afterQk, mmaT_iterNext]
       simp only [mmaT, Bound.Mma.pos]
       (try split_ifs) <;> (try have := Fin.isLt ‹Fin 8›) <;> wt_omega)

theorem kxX_lt {x : WComp.ExitD} (h : wSy (.exit x) = false) : exitT x < kxX x := by
  obtain ⟨site, P⟩ := x
  cases site <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at h <;>
    first | (exfalso; revert h; decide +kernel) | (simp only [kxX, exitT]; omega)

/-- **A silent worker state is timed below its key time.** -/
theorem kxW_lt {L : Launch} {g : Nat} {s : WComp.WSt} (h : wSy s = false)
    (hI : WComp.Inv L g s) : wcompT s < kxW s := by
  cases s with
  | worker d => exact kxWk_lt h
  | idle d =>
    obtain ⟨site, P⟩ := d
    exfalso
    cases site <;> simp only [wSy, isLdRole, WComp.pc, WComp.sub, Bool.or_false] at h <;>
      (revert h; decide +kernel)
  | loader d P => exact kxL_lt h hI.1
  | mma d P => exact kxM_lt h hI.1
  | exit x => exact kxX_lt h

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
