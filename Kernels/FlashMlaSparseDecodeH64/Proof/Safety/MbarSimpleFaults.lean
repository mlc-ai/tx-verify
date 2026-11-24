-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarPublished
import Lemmas.MBarrier.MBarrierInitOrder
import Lemmas.Protocol.ObjectSource
import Lemmas.Protocol.PairTmaRing.ItemFacts

public section

/-! # Barrier initialization and poll faults -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow AsyncCopy MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {m : Loc} {r : Record Ref}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

/-- Each initialization record succeeds at the start of its own object's lifetime. -/
theorem mbar_init_clean (hr : r ∈ X.objects m) {count : Nat} (ha : r.action = .init count)
    : r.fault = none := by
  cases record_source hX.tma.2.2.1 hr with
  | init hid he _ =>
    obtain ⟨r0, h0, hId0, _, hf⟩ := mbar_init_record_first hpre hX hs ht ⟨_, he⟩
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    have hIndex := object_record_index_unique hX.tma.2.2.1 hk h0 (hid.trans hId0.symm)
    rw [hIndex, h0] at hk
    exact (Option.some.inj hk) ▸ hf
  | inval _ _ ha' | arrive _ _ ha' | wait _ _ ha' | increment _ _ ha'
  | tensor _ _ _ ha' | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' | commit _ _ _ ha'
  | clc _ _ _ _ ha' =>
    rw [ha] at ha'
    cases ha'

private theorem ready_before {k : Nat} (hk : (X.objects m)[k]? = some r)
    (hn : ∀ n, r.action ≠ .init n) :
    ∃ st : State, stateBefore (X.objects m) k = some st := by
  have hr := List.mem_of_getElem? hk
  rcases mbar_record_published hpre hX hs ht hr with ⟨⟨n, hAct⟩, _⟩ | ⟨_, _, hi, _⟩
  · exact (hn n hAct).elim
  obtain ⟨r0, h0, _, hAct, hf⟩ := mbar_init_record_first hpre hX hs ht hi
  have hPos : 0 < k := by
    cases k with
    | zero =>
      rw [h0] at hk
      obtain rfl := Option.some.inj hk
      exact (hn _ hAct).elim
    | succ k => omega
  have hNoInv : NoInval (X.objects m) := fun _ hr => mbar_record_not_inval hX hr
  obtain ⟨st, hSt, _⟩ := ObjectInit.checked_expected_after_init (X.objects_checked hX m)
    hNoInv h0 hAct hf hPos (List.getElem?_eq_some_iff.mp hk).1.le
  exact ⟨st, hSt⟩

/-- Every actual parity poll finds its initialized barrier object and succeeds as an operation. -/
theorem mbar_poll_clean (hr : r ∈ X.objects m) {parity : Nat} {success : Bool}
    (ha : r.action = .pollParity parity success) : r.fault = none := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨st, hSt⟩ := ready_before hpre hX hs ht hk (by simp [ha])
  have hOk := (X.objects_checked hX m).at hk
  rw [hSt] at hOk
  unfold RecordOk at hOk
  rw [ha] at hOk
  simpa only [perform, pure, Except.pure] using hOk.2

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
