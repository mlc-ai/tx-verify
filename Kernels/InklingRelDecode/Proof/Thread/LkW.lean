-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkBase

@[expose] public section

/-!
# Warp lockstep: the worker warps (4 to 7)

The machine of a worker thread (`WComp`) runs the worker's prologue and dispatch (`Worker`), then
one of four roles (the loader `Loader`, the MMA warp `Mma`, the idle role `Worker.Idle`, the exit),
and a role's tail returns to the dispatch loop's head (`Worker.Site.loop`). The key of a state is
the position of the next synchronizing state reached from it (`wKey`); a state is synchronizing
(`wSy`) when its instruction is in `syPcs` (named barriers, `bar.warp.sync`, `shfl.sync`,
`elect.sync`, `setmaxnreg`), or when it is the load of the role byte.

## The machines

* **Worker** (`Worker.D`). Forward code `bar0`, `ld0`, `bar1`, `shfl`, then the dispatch loop
  `loop` (`setmaxnreg.inc`), `bar2` (`barrier.sync 1`), `ldRole` (`ld.shared.b8`), which a role's
  return re-enters at `loop`; a role byte above 3 goes through `bad0`, `bad1` (two barriers) back
  to `loop`. Synchronizing: all but `ld0`. The load `ld0` of the Tensor Memory base word is silent
  (its key is the next barrier's). **`ldRole` is made synchronizing:** its successor is steered
  by the loaded role byte, and a key is a function of the state, so the state must be its own key;
  the equality of the two lanes' role indices is the agreement `WAgree` asks there.
* **Idle** (`Worker.Idle.D`). Four barriers and register requests, all synchronizing, straight
  line; the last one's successor is the worker's `loop`.
* **Loader** (`Loader.D`). `setMaxDec`, the vector load `ld0`, `ld1` (silent), `bar0`, then the
  iteration loop `wait` (the `kv_empty` poll, silent: a failed poll loops on its own site) through
  `wb0`, `arrive`, `ldb0`, `wb1`, `el0`..`el3` with their copies and the block-table loads, back
  to `wait`, and after the last iteration `bar1`, `setMaxInc` (whose successor is the worker's
  `loop`). Synchronizing: `setMaxDec`, `bar0`, `wb0`..`wb4`, `el0`..`el3`, `bar1`, `setMaxInc`.
  Lane-dependent branches, both arms with the same key: after `wb0` the lane that arrives on
  `kv_ready` (`arrive`, silent, then `ldb0`) or not; after each `elect.sync` the elected lane's
  guarded copies (silent) or the other lanes' next site. Value-steered branches: `bar0`
  (`n ≤ i`: skip the loop, key `bar1`, or enter it, key of `wait`) and the loop's end after the
  last copy, `n = i + 1` (key `bar1`, or the key of `wait`); the sites `cp3a`, `cp3b` (silent)
  have the key of the branch the counters take, and the agreement is asked at `el3`, which is the
  last synchronizing state before the branch.
* **MMA warp** (`Mma.D`). `setMaxReg`, `ldNum` (silent), `bar0`, then the loop over the QK half
  (`qkBar`, `kvWait` (poll, silent), `qkShfl`, `qkBar2`, `qkElect`, the elected lane's eight MMAs
  and commit, all silent), the PV half (`pvBar`, `pWait`, `pvShfl`, `pvBar2`, `pvElect`, the
  elected lane's MMAs and two commits, silent), and after the loop `finBar`, `finElect`,
  `finCommit` (silent), `bar1`, `setMaxRegInc` (whose successor is the worker's `loop`).
  Lane-dependent branches: the elected lane runs the guarded block, the others skip it; both
  continue at the same site (`afterQk`, `iterNext`, or `bar1`). Value-steered branches: `bar0`
  (the loop runs or not: `Mma.start`), and the successor of the QK half (`Mma.afterQk`) and of
  the PV half (`Mma.iterNext`), which depend on the iteration `i` and `num_iters` `n`. The sites of
  the guarded blocks (`qk j`, `qkCommit`, `pv j`, `pvCommit1`, `pvCommit2`) are silent and have the
  key of the site the half ends at; the agreement is asked at `qkElect` and `pvElect`.
* **Exit** (`WComp.ExitD`). `bar.sync 0` (synchronizing) and `ret` (no successor).

## The agreement

`WAgree` is the weakest relation between two lanes' states and events at synchronizing states with
the same key under which the successors have the same key: a conjunction over the sites that is
`True` where the successor's key needs no agreement. It says

* at `ldRole`: the two lanes' loaded role bytes lead to the same role site (`roleIdx`; from
  `Interface.RoleReads`, the role byte is read from the word the default partition wrote);
* at the loader's `bar0`: `n ≤ i` has the same truth value for both lanes (the loaded
  `(num_pre, num_iters)`);
* at the loader's `el3`: `n = i + 1` has the same truth value (the loop's last iteration);
* at the MMA warp's `bar0`, `qkElect`, `pvElect`: the loop's next site (`Mma.start`,
  `Mma.afterQk`, `Mma.iterNext`) is the same for both lanes (`num_iters` and the iteration);
* at every MMA state: neither lane is at `qkSkip` or `pvSkip` (the branch after a broadcast is
  taken only on a word other than 7, which warp 7 does not receive).

No invariant is assumed.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### Keys -/

/-- The key of a worker state: the next synchronizing position. The load of the role byte is its
own key (it is a synchronizing state). -/
def wkW (d : Worker.D) : Nat :=
  match d.site with
  | .ldRole => Worker.Site.ldRole.pc
  | s => keyPc s.pc 0

/-- The key of an idle state. -/
def wkI (d : Worker.Idle.D) : Nat := keyPc d.site.pc 0

/-- The key of a loader state. The sites after the last copy's election (`cp3a`, `cp3b`) end at
`bar1` after the last iteration and at the poll otherwise. -/
def wkL (d : Loader.D) : Nat :=
  match d.site with
  | .cp3a | .cp3b =>
    if d.n = (d.i + 1) % 2 ^ 32 then keyPc Loader.Site.bar1.pc 0 else keyPc Loader.Site.wait.pc 0
  | s => keyPc s.pc (Loader.sub d)

/-- The key of an MMA state. The elected lane's blocks end at the site the half's successor
(`afterQk`, `iterNext`) gives. -/
def wkM (d : Mma.D) : Nat :=
  match d.site with
  | .qk _ | .qkCommit => keyPc (Mma.afterQk d).site.pc 0
  | .pv _ | .pvCommit1 | .pvCommit2 => keyPc (Mma.iterNext d).site.pc 0
  | s => keyPc s.pc 0

/-- The key of an exit state. -/
def wkX (x : WComp.ExitD) : Nat := keyPc x.site.pc 0

/-- The state is the load of the role byte. -/
def isLdRole : WComp.WSt → Bool
  | .worker ⟨.ldRole, _⟩ => true
  | _ => false

/-- The state's event is synchronizing: its instruction is in `syPcs`, or it is the load of the
role byte. -/
def wSy (s : WComp.WSt) : Bool :=
  syAt (WComp.pc s) (WComp.sub s) || isLdRole s

/-- The position of the next synchronizing state of a worker thread's state. -/
def wKey (_L : Launch) (_g : Nat) : WComp.WSt → Nat
  | .worker d => wkW d
  | .idle d => wkI d
  | .loader d _ => wkL d
  | .mma d _ => wkM d
  | .exit x => wkX x

/-! ### The agreement -/

/-- The role the load of the role byte sends the thread to: the site of the worker's dispatch
(`Worker.next` at `ldRole`), a function of the loaded byte. -/
def roleIdx (L : Launch) (g : Nat) (d : Worker.D) (e : Event) : Option (Option Worker.Site) :=
  (Worker.next L g d e).map (Option.map Worker.D.site)

/-- What two loader lanes at one synchronizing state agree on: the signed entry test of the loop
at `bar0`, the test of the last iteration at `el3`. -/
def LdAgree (d d' : Loader.D) : Prop :=
  (d.site = .bar0 → (Loader.sxI d.n ≤ Loader.sxI d.i ↔ Loader.sxI d'.n ≤ Loader.sxI d'.i)) ∧
    (d.site = .el3 → (d.n = (d.i + 1) % 2 ^ 32 ↔ d'.n = (d'.i + 1) % 2 ^ 32))

/-- **What two lanes' states and events at synchronizing states of equal key agree on.** Only
the steering sites ask for anything, as a relation between the two lanes' own fields.

* worker `ldRole`: the loaded role bytes lead to the same role site (`roleIdx`);
* loader `bar0`: `n ≤ i` as signed words has one truth value (the loaded
  `(num_pre, num_iters)`);
* loader `el3`: `n = i + 1` (modulo `2 ^ 32`) has one truth value (the last iteration);
* MMA `bar0`: `Mma.start` leads to one site (the loaded `num_iters` and the loop's bound);
* MMA `qkElect`: `Mma.afterQk` leads to one site (the iteration `i` and `num_iters`);
* MMA `pvElect`: `Mma.iterNext` leads to one site (the iteration `i` and `num_iters`);
* every MMA state: neither lane is at the barrier of a lane that skips a half (`qkSkip`,
  `pvSkip`; the broadcast word of warp 7 is 7). -/
def WAgree (L : Launch) (g h : Nat) : WComp.WSt → WComp.WSt → Event → Event → Prop
  | .worker d, .worker d', e, e' =>
    d.site = .ldRole → roleIdx L g d e = roleIdx L h d' e'
  | .loader d _, .loader d' _, _, _ => LdAgree d d'
  | .mma d _, .mma d' _, _, _ =>
    d.site.isSkip = false ∧ d'.site.isSkip = false ∧
    (d.site = .bar0 → (Mma.start d).site = (Mma.start d').site) ∧
      (d.site = .qkElect → (Mma.afterQk d).site = (Mma.afterQk d').site) ∧
      (d.site = .pvElect → (Mma.iterNext d).site = (Mma.iterNext d').site)
  | _, _, _, _ => True

variable {L : Launch} {g h : Nat}

/-! ### The first state and the synchronizing keys -/

/-- **The first states of the lanes of a warp have one key**: it is the first barrier's position,
whatever the inherited registers. -/
theorem w_init (Q : Params) (_hw : SameWarp L g h) :
    wKey L g (WComp.code L g Q).init = wKey L h (WComp.code L h Q).init := by
  rfl

/-- **A synchronizing state is its own key.** -/
theorem w_sy_key {s : WComp.WSt} (hs : wSy s = true) : wKey L g s = WComp.pc s := by
  cases s with
  | worker d =>
    obtain ⟨site, P⟩ := d
    cases site <;> simp only [wSy, isLdRole, wKey, wkW, WComp.pc, WComp.sub,
      Bool.or_eq_true] at hs ⊢ <;>
      (revert hs; decide +kernel)
  | idle d =>
    obtain ⟨site, P⟩ := d
    cases site <;> simp only [wSy, isLdRole, wKey, wkI, WComp.pc, WComp.sub,
      Bool.or_false] at hs ⊢ <;>
      (revert hs; decide +kernel)
  | loader d P =>
    obtain ⟨site, pro, i, n, p0, p1, ln⟩ := d
    cases site <;> simp only [wSy, isLdRole, wKey, wkL, WComp.pc, WComp.sub, Loader.sub,
      Bool.or_false] at hs ⊢ <;>
      first | (revert hs; decide +kernel) | (exfalso; revert hs; decide +kernel)
  | mma d P =>
    obtain ⟨site, i, n, tm, pro⟩ := d
    cases site <;> simp only [wSy, isLdRole, wKey, wkM, WComp.pc, WComp.sub,
      Bool.or_false] at hs ⊢ <;>
      first
        | (revert hs; decide +kernel)
        | (exfalso; revert hs; decide +kernel)
        | (exfalso; rename_i j; revert hs j; decide +kernel)
  | exit x =>
    obtain ⟨site, P⟩ := x
    cases site <;> simp only [wSy, isLdRole, wKey, wkX, WComp.pc, WComp.sub,
      Bool.or_false] at hs ⊢ <;>
      (revert hs; decide +kernel)

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
