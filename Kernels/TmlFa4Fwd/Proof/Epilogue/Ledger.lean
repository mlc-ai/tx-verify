-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's ledger

The output warp's tensor stores, bulk-group commits, read waits, arrivals and successful polls of
each stage's ready barrier are counted by the thread machine's ghost ledger (`Cls`). Their closed
forms are functions of the role's state (`stores`, `commits`, `drains`, `frees`, `acqd`): four
stores and one commit per stage, one poll and one arrival per stage, two read waits, all of them
once the tile is written. `Led` states them as a conjunct of the reference invariant, and
`led_step` carries them along a step, from the shape table. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A store (or undefined behaviour) is of no other class the output warp counts. -/
theorem store_cls {L : Launch} {g : Nat} {e : Event} (h : isStore e = true) :
    isCommit e = false ∧ isWait e = false ∧ isArrive e = false ∧
      ∀ st, okPoll (readyLoc L g st) e = false ∧ arrivesOn (freeLoc L g st) e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [isStore, isCommit, isWait, isArrive, sourceWaitSuccess, sourceArrive]

/-- Whether the output tile is written before a site: the writeback's stage, and the second
pass. -/
def written : Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .exit l => l
  | _ => false

/-- The tensor stores before state `d`. -/
def stores (d : D) : Nat :=
  match d.site with
  | .store st b => 4 * st.val + b.val
  | .commit st => 4 * (st.val + 1)
  | .ready st => 4 * st.val
  | .drain _ | .free _ => 8
  | s => if written s then 8 else 0

/-- The bulk-group commits before state `d`. -/
def commits (d : D) : Nat :=
  match d.site with
  | .ready st | .store st _ | .commit st => st.val
  | .drain _ | .free _ => 2
  | s => if written s then 2 else 0

/-- The arrivals before state `d`: one per stage freed. -/
def frees (d : D) : Nat :=
  match d.site with
  | .free st | .drain st => st.val
  | s => if written s then 2 else 0

/-- The read waits before state `d`. -/
def drains (d : D) : Nat :=
  match d.site with
  | .drain st => st.val
  | .free st => st.val + 1
  | s => if written s then 2 else 0

/-- The successful polls of stage `st` before state `d`. -/
def acqd (st : Fin 2) (d : D) : Nat :=
  match d.site with
  | .ready s => if st.val < s.val then 1 else 0
  | .store s _ | .commit s => if st.val ≤ s.val then 1 else 0
  | .drain _ | .free _ => 1
  | s => if written s then 1 else 0

/-- The arrivals on stage `st`'s free barrier before state `d`: one once the stage is freed. -/
def freedAt (st : Fin 2) (d : D) : Nat := if st.val < frees d then 1 else 0

/-- **The output warp's ledger at a state**: the thread machine's counts of the output warp's
classes are the state's counts. -/
def Led (n : Cls → Nat) (d : D) : Prop :=
  n .store = stores d ∧ n .commit = commits d ∧ n .wait = drains d ∧ n .arrive = frees d ∧
    ∀ st, n (.poll st) = acqd st d ∧ n (.freed st) = freedAt st d

variable {p : Params} {L : Launch} {g : Nat} {ent : Nat → Value}

set_option maxHeartbeats 1000000 in
/-- **The ledger steps with the machine**: the counts the event adds are the state's. -/
theorem led_step {n : Cls → Nat} {d d' : D} {e : Event} (hL : Led n d) (hev : Ev p L g d e)
    (hn : (code p L g ent).next d e = some (some d')) : Led (Code.bump (cls L g) n e) d' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hL
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  simp only [Led, Code.bump, cls, h1, h2, h3, h4, h5]
  shape_cases s at hev hn unfolding [Ev]
    trans [code, succ, word32, afterTotal, loopHead, scanExit, afterTiles, storeNext]
  all_goals try (simp only [Option.map_some, Option.some.injEq] at hn; subst hn)
  all_goals try (have := store_cls (L := L) (g := g) hev)
  all_goals simp_all [stores, commits, drains, frees, acqd, freedAt, isStore, isCommit, isWait,
    isArrive, sourceWaitSuccess, sourceArrive, written, Scan.late, loopOf, readyLoc, freeLoc]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
