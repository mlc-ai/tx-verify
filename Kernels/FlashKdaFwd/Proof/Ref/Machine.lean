-- SPDX-License-Identifier: Apache-2.0
-- The equations are written by Gen/ref_machine.py.
module

public import Kernels.FlashKdaFwd.Proof.Thread.Entry
public import Kernels.FlashKdaFwd.Proof.Thread.ParamBridge
public import Kernels.FlashKdaFwd.Proof.Ref.Common

@[expose] public section

/-! # The successor of the thread machine at the sites of the startup phase, by form

The generated machine (`Thread/Next.lean`) states the successor at each site with its own
`match` on the event. The reference layer reads a successor through five named forms, so that
one lemma per form says what a successor means for the event and the next state:

* a plain successor `some (some d')`, whatever the event (initializations, fences, barriers,
  arrivals, tensor copies);
* `loadWord` (the generator's own, `Thread/EventLib.lean`): a load of the offsets array; bytes
  that rebuild to no value stop the thread, a 64-bit integer continues with the word, any
  other value is the machine's only give-up (excluded by the assumption `inputReadOnly`);
* `elNext` and `elNextB`: an election; the successor depends on the elected lane and on
  whether the thread's lane is the elected one (stated with `if` at the first four elections
  and with a Boolean at the fifth, as the generator writes them);
* `shNext`: a shuffle whose received value the code reads as an integer;
* `wtNext`: a poll of an mbarrier.

`nextR_<site>` is the equation of each of the 64 sites of the phase in its form, by `rfl` from
the generated definition. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

noncomputable section

/-- The successor after an election: the elected lane goes to `f ld true`, the others to
`f ld false`. -/
def elNext (L : Launch) (g : Nat) (e : Event) (f : Nat → Bool → D) : Option (Option D) :=
  match e.kind with
  | .elect _ _ ld => some (some (if laneOf L g = ld then f ld true else f ld false))
  | _ => none

/-- The successor after an election, with "this lane is the elected one" as a Boolean. -/
def elNextB (L : Launch) (g : Nat) (e : Event) (f : Nat → Bool → D) : Option (Option D) :=
  match e.kind with
  | .elect _ _ ld => some (some (f ld (laneOf L g == ld)))
  | _ => none

/-- The successor after a shuffle whose received value is read as an integer. -/
def shNext (e : Event) (f : BitVec 64 → Bool → D) : Option (Option D) :=
  match e.kind with
  | .shfl _ _ _ _ v ok =>
    match wordOf v with
    | some n => some (some (f (BitVec.ofNat 64 n) ok))
    | none => none
  | _ => none

/-- The successor after a poll of an mbarrier. -/
def wtNext (e : Event) (f : Bool → D) : Option (Option D) :=
  match e.kind with
  | .wait _ _ ok _ _ => some (some (f ok))
  | _ => none

variable {L : Launch} {g : Nat} (w : Nat → BitVec 64) (p : Nat → Bool) (x : Nat → Value)
  (e : Event)


theorem nextR_elect_0 : Thread.next L g ⟨.elect 0, w, p, x⟩ e =
    elNext L g e fun ld b =>
      after_elect_0 L g (scope_elect_0 ⟨.elect 0, w, p, x⟩ ld b) := rfl

theorem nextR_elect_1 : Thread.next L g ⟨.elect 1, w, p, x⟩ e =
    elNext L g e fun ld b =>
      after_elect_1 L g (scope_elect_1 ⟨.elect 1, w, p, x⟩ ld b) := rfl

theorem nextR_elect_2 : Thread.next L g ⟨.elect 2, w, p, x⟩ e =
    elNext L g e fun ld b =>
      after_elect_2 L g (scope_elect_2 ⟨.elect 2, w, p, x⟩ ld b) := rfl

theorem nextR_elect_3 : Thread.next L g ⟨.elect 3, w, p, x⟩ e =
    elNext L g e fun ld b =>
      after_elect_3 L g (scope_elect_3 ⟨.elect 3, w, p, x⟩ ld b) := rfl

theorem nextR_elect_4 : Thread.next L g ⟨.elect 4, w, p, x⟩ e =
    elNextB L g e fun ld b =>
      after_elect_4 L g (scope_elect_4 ⟨.elect 4, w, p, x⟩ ld b) := rfl

theorem nextR_shfl_0 : Thread.next L g ⟨.shfl 0, w, p, x⟩ e =
    (match e.kind with
    | .shfl _ _ _ _ _ ok => some (some (after_shfl_0 L g ⟨.shfl 0, w, p, x⟩ 0 ok))
    | _ => none) := rfl

theorem nextR_shfl_1 : Thread.next L g ⟨.shfl 1, w, p, x⟩ e =
    shNext e fun n ok => after_shfl_1 L g ⟨.shfl 1, w, p, x⟩ n ok := rfl

theorem nextR_shfl_2 : Thread.next L g ⟨.shfl 2, w, p, x⟩ e =
    shNext e fun n ok => after_shfl_2 L g ⟨.shfl 2, w, p, x⟩ n ok := rfl

theorem nextR_mbarInit_0 : Thread.next L g ⟨.mbarInit 0, w, p, x⟩ e =
    some (some (after_mbarInit_0 L g ⟨.mbarInit 0, w, p, x⟩)) := rfl

theorem nextR_mbarInit_1 : Thread.next L g ⟨.mbarInit 1, w, p, x⟩ e =
    some (some (after_mbarInit_1 L g ⟨.mbarInit 1, w, p, x⟩)) := rfl

theorem nextR_mbarInit_2 : Thread.next L g ⟨.mbarInit 2, w, p, x⟩ e =
    some (some (after_mbarInit_2 L g ⟨.mbarInit 2, w, p, x⟩)) := rfl

theorem nextR_mbarInit_3 : Thread.next L g ⟨.mbarInit 3, w, p, x⟩ e =
    some (some (after_mbarInit_3 L g ⟨.mbarInit 3, w, p, x⟩)) := rfl

theorem nextR_mbarInit_4 : Thread.next L g ⟨.mbarInit 4, w, p, x⟩ e =
    some (some (after_mbarInit_4 L g ⟨.mbarInit 4, w, p, x⟩)) := rfl

theorem nextR_mbarInit_5 : Thread.next L g ⟨.mbarInit 5, w, p, x⟩ e =
    some (some (after_mbarInit_5 L g ⟨.mbarInit 5, w, p, x⟩)) := rfl

theorem nextR_mbarInit_6 : Thread.next L g ⟨.mbarInit 6, w, p, x⟩ e =
    some (some (after_mbarInit_6 L g ⟨.mbarInit 6, w, p, x⟩)) := rfl

theorem nextR_mbarInit_7 : Thread.next L g ⟨.mbarInit 7, w, p, x⟩ e =
    some (some (after_mbarInit_7 L g ⟨.mbarInit 7, w, p, x⟩)) := rfl

theorem nextR_mbarInit_8 : Thread.next L g ⟨.mbarInit 8, w, p, x⟩ e =
    some (some (after_mbarInit_8 L g ⟨.mbarInit 8, w, p, x⟩)) := rfl

theorem nextR_mbarInit_9 : Thread.next L g ⟨.mbarInit 9, w, p, x⟩ e =
    some (some (after_mbarInit_9 L g ⟨.mbarInit 9, w, p, x⟩)) := rfl

theorem nextR_mbarInit_10 : Thread.next L g ⟨.mbarInit 10, w, p, x⟩ e =
    some (some (after_mbarInit_10 L g ⟨.mbarInit 10, w, p, x⟩)) := rfl

theorem nextR_fenceMbarInit_0 : Thread.next L g ⟨.fenceMbarInit 0, w, p, x⟩ e =
    some (some (after_fenceMbarInit_0 L g ⟨.fenceMbarInit 0, w, p, x⟩)) := rfl

theorem nextR_fenceMbarInit_1 : Thread.next L g ⟨.fenceMbarInit 1, w, p, x⟩ e =
    some (some (after_fenceMbarInit_1 L g ⟨.fenceMbarInit 1, w, p, x⟩)) := rfl

theorem nextR_fenceMbarInit_2 : Thread.next L g ⟨.fenceMbarInit 2, w, p, x⟩ e =
    some (some (after_fenceMbarInit_2 L g ⟨.fenceMbarInit 2, w, p, x⟩)) := rfl

theorem nextR_bar_0 : Thread.next L g ⟨.bar 0, w, p, x⟩ e =
    some (some (after_bar_0 L g ⟨.bar 0, w, p, x⟩)) := rfl

theorem nextR_bar_1 : Thread.next L g ⟨.bar 1, w, p, x⟩ e =
    some (some (after_bar_1 L g ⟨.bar 1, w, p, x⟩)) := rfl

theorem nextR_bar_2 : Thread.next L g ⟨.bar 2, w, p, x⟩ e =
    some (some (after_bar_2 L g ⟨.bar 2, w, p, x⟩)) := rfl

theorem nextR_load_0 : Thread.next L g ⟨.load 0, w, p, x⟩ e =
    loadWord e fun y => after_load_0 L g ⟨.load 0, w, p, x⟩ y := rfl

theorem nextR_load_1 : Thread.next L g ⟨.load 1, w, p, x⟩ e =
    loadWord e fun y => after_load_1 L g ⟨.load 1, w, p, x⟩ y := rfl

theorem nextR_load_2 : Thread.next L g ⟨.load 2, w, p, x⟩ e =
    loadWord e fun y => after_load_2 L g ⟨.load 2, w, p, x⟩ y := rfl

theorem nextR_load_3 : Thread.next L g ⟨.load 3, w, p, x⟩ e =
    loadWord e fun y => after_load_3 L g ⟨.load 3, w, p, x⟩ y := rfl

theorem nextR_load_4 : Thread.next L g ⟨.load 4, w, p, x⟩ e =
    loadWord e fun y => after_load_4 L g ⟨.load 4, w, p, x⟩ y := rfl

theorem nextR_load_5 : Thread.next L g ⟨.load 5, w, p, x⟩ e =
    loadWord e fun y => after_load_5 L g ⟨.load 5, w, p, x⟩ y := rfl

theorem nextR_load_6 : Thread.next L g ⟨.load 6, w, p, x⟩ e =
    loadWord e fun y => after_load_6 L g ⟨.load 6, w, p, x⟩ y := rfl

theorem nextR_load_7 : Thread.next L g ⟨.load 7, w, p, x⟩ e =
    loadWord e fun y => after_load_7 L g ⟨.load 7, w, p, x⟩ y := rfl

theorem nextR_load_8 : Thread.next L g ⟨.load 8, w, p, x⟩ e =
    loadWord e fun y => after_load_8 L g ⟨.load 8, w, p, x⟩ y := rfl

theorem nextR_load_9 : Thread.next L g ⟨.load 9, w, p, x⟩ e =
    loadWord e fun y => after_load_9 L g ⟨.load 9, w, p, x⟩ y := rfl

theorem nextR_load_10 : Thread.next L g ⟨.load 10, w, p, x⟩ e =
    loadWord e fun y => after_load_10 L g ⟨.load 10, w, p, x⟩ y := rfl

theorem nextR_load_11 : Thread.next L g ⟨.load 11, w, p, x⟩ e =
    loadWord e fun y => after_load_11 L g ⟨.load 11, w, p, x⟩ y := rfl

theorem nextR_load_12 : Thread.next L g ⟨.load 12, w, p, x⟩ e =
    loadWord e fun y => after_load_12 L g ⟨.load 12, w, p, x⟩ y := rfl

theorem nextR_load_13 : Thread.next L g ⟨.load 13, w, p, x⟩ e =
    loadWord e fun y => after_load_13 L g ⟨.load 13, w, p, x⟩ y := rfl

theorem nextR_load_14 : Thread.next L g ⟨.load 14, w, p, x⟩ e =
    loadWord e fun y => after_load_14 L g ⟨.load 14, w, p, x⟩ y := rfl

theorem nextR_load_15 : Thread.next L g ⟨.load 15, w, p, x⟩ e =
    loadWord e fun y => after_load_15 L g ⟨.load 15, w, p, x⟩ y := rfl

theorem nextR_load_16 : Thread.next L g ⟨.load 16, w, p, x⟩ e =
    loadWord e fun y => after_load_16 L g ⟨.load 16, w, p, x⟩ y := rfl

theorem nextR_load_17 : Thread.next L g ⟨.load 17, w, p, x⟩ e =
    loadWord e fun y => after_load_17 L g ⟨.load 17, w, p, x⟩ y := rfl

theorem nextR_load_18 : Thread.next L g ⟨.load 18, w, p, x⟩ e =
    loadWord e fun y => after_load_18 L g ⟨.load 18, w, p, x⟩ y := rfl

theorem nextR_load_19 : Thread.next L g ⟨.load 19, w, p, x⟩ e =
    loadWord e fun y => after_load_19 L g ⟨.load 19, w, p, x⟩ y := rfl

theorem nextR_load_20 : Thread.next L g ⟨.load 20, w, p, x⟩ e =
    loadWord e fun y => after_load_20 L g ⟨.load 20, w, p, x⟩ y := rfl

theorem nextR_mbarArrive_0 : Thread.next L g ⟨.mbarArrive 0, w, p, x⟩ e =
    some (some (after_mbarArrive_0 L g ⟨.mbarArrive 0, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_0 : Thread.next L g ⟨.tensorCopy 0, w, p, x⟩ e =
    some (some (after_tensorCopy_0 L g ⟨.tensorCopy 0, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_1 : Thread.next L g ⟨.tensorCopy 1, w, p, x⟩ e =
    some (some (after_tensorCopy_1 L g ⟨.tensorCopy 1, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_2 : Thread.next L g ⟨.tensorCopy 2, w, p, x⟩ e =
    some (some (after_tensorCopy_2 L g ⟨.tensorCopy 2, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_3 : Thread.next L g ⟨.tensorCopy 3, w, p, x⟩ e =
    some (some (after_tensorCopy_3 L g ⟨.tensorCopy 3, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_4 : Thread.next L g ⟨.tensorCopy 4, w, p, x⟩ e =
    some (some (after_tensorCopy_4 L g ⟨.tensorCopy 4, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_5 : Thread.next L g ⟨.tensorCopy 5, w, p, x⟩ e =
    some (some (after_tensorCopy_5 L g ⟨.tensorCopy 5, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_6 : Thread.next L g ⟨.tensorCopy 6, w, p, x⟩ e =
    some (some (after_tensorCopy_6 L g ⟨.tensorCopy 6, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_7 : Thread.next L g ⟨.tensorCopy 7, w, p, x⟩ e =
    some (some (after_tensorCopy_7 L g ⟨.tensorCopy 7, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_8 : Thread.next L g ⟨.tensorCopy 8, w, p, x⟩ e =
    some (some (after_tensorCopy_8 L g ⟨.tensorCopy 8, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_9 : Thread.next L g ⟨.tensorCopy 9, w, p, x⟩ e =
    some (some (after_tensorCopy_9 L g ⟨.tensorCopy 9, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_10 : Thread.next L g ⟨.tensorCopy 10, w, p, x⟩ e =
    some (some (after_tensorCopy_10 L g ⟨.tensorCopy 10, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_11 : Thread.next L g ⟨.tensorCopy 11, w, p, x⟩ e =
    some (some (after_tensorCopy_11 L g ⟨.tensorCopy 11, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_12 : Thread.next L g ⟨.tensorCopy 12, w, p, x⟩ e =
    some (some (after_tensorCopy_12 L g ⟨.tensorCopy 12, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_13 : Thread.next L g ⟨.tensorCopy 13, w, p, x⟩ e =
    some (some (after_tensorCopy_13 L g ⟨.tensorCopy 13, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_14 : Thread.next L g ⟨.tensorCopy 14, w, p, x⟩ e =
    some (some (after_tensorCopy_14 L g ⟨.tensorCopy 14, w, p, x⟩)) := rfl

theorem nextR_tensorCopy_15 : Thread.next L g ⟨.tensorCopy 15, w, p, x⟩ e =
    some (some (after_tensorCopy_15 L g ⟨.tensorCopy 15, w, p, x⟩)) := rfl

theorem nextR_mbarWait_0 : Thread.next L g ⟨.mbarWait 0, w, p, x⟩ e =
    wtNext e fun ok => after_mbarWait_0 L g ⟨.mbarWait 0, w, p, x⟩ ok := rfl

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref
