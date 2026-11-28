-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticPoll
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.NotThreadFence
public import Lemmas.Flow.PollFacts
public import Lemmas.Order.GuardSnoc

@[expose] public section

/-! # Guarded synchronization

The decoded program has no releasing store, no atomic and no thread fence (static scans, evaluated
once), and every poll spins (`poll_canonical`); so synchronization is guarded where no mbarrier
record faults (`guardedOfNoObjectFault`). The form is tml-fa4's (`Lib/Guarded.lean`), restated on
this kernel's program. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

private theorem noReleaseCode : kernel.code.all (fun ins => !PTX.releaseOp ins.op) = true := by
  decide +kernel

/-- No write releases. -/
theorem noReleasingStore (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat} {a : Acc}
    {bs : List Byte} (he : X.get i = some ⟨pc, .wr a bs⟩) : a.release = false := by
  rcases get_source hX he with ⟨_, hu⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hu
  have hOp : PTX.releaseOp ins.op = false := by
    simpa using List.all_eq_true.mp noReleaseCode ins (List.mem_of_getElem? hc)
  exact fires_write_release hf hOp rfl

private theorem noAtomicCode : kernel.code.all (fun ins => !atomicOp ins.op) = true := by
  decide +kernel

/-- No event is an atomic. -/
theorem noAtomicEvent (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat} {a : Acc}
    {old : List (Option Byte)} {new : Option (List Byte)}
    (he : X.get i = some ⟨pc, .rmw a old new⟩) : False :=
  no_kind_of_code hX atomicOp (fun k => ∃ a old new, k = .rmw a old new)
    (fun _ ⟨_, _, _, hk⟩ => by cases hk)
    (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk) noAtomicCode he ⟨_, _, _, rfl⟩

private theorem noThreadFenceCode :
    kernel.code.all (fun ins => !threadFenceOp ins.op) = true := by
  decide +kernel

/-- No event is a thread fence. -/
theorem noThreadFence (hX : Consistent l kernel A m X) {i : EvId} {s : FenceSem}
    {scope : MbarScope} : ¬ X.ThreadFence i s scope := by
  rintro ⟨_, he⟩
  exact no_kind_of_code hX threadFenceOp (fun k => ∃ s scope, k = .fence s scope)
    (fun _ ⟨_, _, hk⟩ => by cases hk)
    (fun hf ⟨_, _, hk⟩ => fires_threadFence_op hf hk) noThreadFenceCode he ⟨_, _, rfl⟩

/-- **Fault-free object histories make synchronization guarded.** -/
theorem guardedOfNoObjectFault (hX : Consistent l kernel A m X)
    (hf : ∀ mb r, r ∈ X.objects mb → r.fault = none) : SyncGuarded l kernel X where
  spin _ _ _ _ _ _ he := poll_canonical hX he
  noMemSync i j := ⟨noSynchronizesWith_of (fun _ _ _ _ he => noReleasingStore hX he)
    (fun _ _ _ _ _ he => (noAtomicEvent hX he).elim) i j,
    not_fenceSync_of_noFence (fun _ _ _ => noThreadFence hX) i j⟩
  noFault mb _ _ r _ hr _ _ _ := hf mb r (List.mem_of_getElem? hr)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
