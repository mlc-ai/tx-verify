-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local
public import Core.Sync.WarpInstance

@[expose] public section

/-!
# Active-mask events and values

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## THREAD-ACTIVEMASK — active-thread query
Statement: `activemask` produces an event that returns a 32-bit mask, which is written to the
  destination as a 32-bit integer.

Defs: activemaskTmpl

Source:
- §9.7.15.12 (activemask): "activemask queries predicated-on active threads from the executing warp
    and sets the destination d with 32-bit integer mask where bit position in the mask corresponds
    to the thread’s laneid ."
- §9.7.15.12 (activemask): "Destination d is a 32-bit destination register."

Direction: equal

Applies: `activemask.b32`

Premises: None.

Effect: Event production; the mask is constrained by DEP-WARP-ACTIVEMASK.
-/

/-- Active-thread query (ACTIVEMASK). -/
def activemaskTmpl (t : TState) (d : Nat) : Tmpl :=
  .activemask (fun r => next (setReg t d (.bits 32 (r.setWidth 64))))

/-! ## DEP-WARP-ACTIVEMASK — the mask of active threads

Statement: The mask that `activemask` returns has the bit of the executing lane set and the bit of
  every lane with no thread clear. The bits of the other lanes of the warp are unconstrained. The
  query waits for no other lane and orders no memory operation.

Defs: ActiveMaskOk

Source:
- §9.7.15.12 (activemask): "An active thread will contribute 1 for its entry in the result and
    exited or inactive or predicated-off thread will contribute 0 for its entry in the result."
- §3.2: "A schedule optimizer determines how to group active threads from the same warp together
    into SIMT units"

Direction: stricter

Applies: Every `activemask` event

Premises: An `activemask` event exists.

Effect: Execution constraint in `Consistent.warpValue`. The executing thread is active and its guard
  is true, so its bit is set. Which other lanes are active is decided by the schedule optimizer
  (§3.2) and is not determined by the program, so every value of their bits is kept, including a set
  bit for a lane that has exited (stricter). A lane with no thread (the last warp of a CTA whose
  size is not a multiple of 32) is never active.
-/

/-- Every `activemask` result names the executing lane and only lanes that are threads of its
warp. -/
def ActiveMaskOk (X : Execution) : Prop :=
  ∀ g i pc r, X.get (g, i) = some ⟨pc, .activemask r⟩ →
    r.getLsbD (laneOf L g) = true ∧ maskInWarp L g r.toNat

end

end PTX
