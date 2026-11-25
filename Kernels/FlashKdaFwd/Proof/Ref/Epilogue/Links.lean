-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Interface
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Inv
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Inv
public import Kernels.FlashKdaFwd.Proof.Ref.Store.Inv

@[expose] public section

/-! # Epilogue phase: the exits of the three tile loops give its entry

The entry condition of the epilogue (`In`, `Interface.lean`: the site `bar_7`, the thread index
in `%r1736`, the flag `%p77`, the election flag `%r180` in the store warp, and six
`bar.sync 0`) follows from the exit condition of each of the three tile-loop phases at the same
state and trace position:

* `in_of_compute`: from `Compute.Out` (a compute thread; the role is part of `Compute.Exit`);
* `in_of_producer`: from `Producer.Out`, for a thread of the load warp (`warp g = 4`: the
  Producer's exit condition does not state the role, the chain of a thread of the load warp
  knows it);
* `in_of_store`: from `Store.Out` (the role is `Store.Keep.store`).

Each reads the registers off the phase's `Exit` and the six `bar.sync 0` off the first field of
the phase's exit ledger. These are the `hlink` hypotheses of `Ref/Chain.lean:
Phase.Traces.seq` for the pairs (tile loop, epilogue). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref

noncomputable section

variable {P : Params} {L : Launch} {X : Execution} {g : Nat}

/-- The exit of the Compute phase is the entry of the epilogue. -/
theorem in_of_compute {j0 k : Nat} {d : D} (h : Compute.Out P L X g j0 k d) :
    In P X g k d := by
  obtain ⟨hx, hl, -⟩ := h
  refine ⟨entry_of_compute hx.compute hx.site hx.tid hx.p77, ?_⟩
  have h6 := congrArg Compute.Led.bar0 hl
  exact h6

/-- The exit of the Producer phase is the entry of the epilogue, for a thread of the load
warp. -/
theorem in_of_producer (hw : warp g = 4) {k : Nat} {d : D} (h : Producer.Out P L X g k d) :
    In P X g k d := by
  obtain ⟨hx, hl⟩ := h
  refine ⟨entry_of_load hw hx.site hx.tid hx.p77, ?_⟩
  have h6 := congrArg Producer.Led.bars hl
  rw [Producer.ledExit] at h6
  split at h6 <;> exact h6

/-- The exit of the Store phase is the entry of the epilogue. -/
theorem in_of_store {k : Nat} {d : D} (h : Store.Out P X g k d) : In P X g k d := by
  obtain ⟨hx, hl⟩ := h
  refine ⟨entry_of_store hx.keep.store hx.site hx.tid' hx.role hx.keep.elected, ?_⟩
  have h6 := congrArg Store.Led.bars hl
  rw [Store.ledExit] at h6
  split at h6 <;> exact h6

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
