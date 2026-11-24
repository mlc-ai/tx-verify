-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.PollSpin
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.NotThreadFence

@[expose] public section

/-! # Guarded synchronization

The code has no releasing store, no atomic and no thread fence, and every poll spins
(`poll_canonical`); so synchronization is guarded where no mbarrier record faults
(`guardedOfNoObjectFault`, `guardedOfTmaSafe`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

private theorem noReleaseCode : kernel.code.all (fun ins => !PTX.releaseOp ins.op) = true := by
  decide +kernel

theorem noReleasingStore (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat} {a : Acc}
    {bs : List Byte} (he : X.get i = some ⟨pc, .wr a bs⟩) : a.release = false := by
  rcases get_source hX he with ⟨_, hu⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hu
  have hOp : PTX.releaseOp ins.op = false := by
    simpa using List.all_eq_true.mp noReleaseCode ins (List.mem_of_getElem? hc)
  exact fires_write_release hf hOp rfl

private theorem noAtomicCode : kernel.code.all (fun ins => !atomicOp ins.op) = true := by
  decide +kernel

theorem noAtomicEvent (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat} {a : Acc}
    {old : List (Option Byte)} {new : Option (List Byte)} (he : X.get i = some ⟨pc, .rmw a old new⟩)
    : False :=
  no_kind_of_code hX atomicOp (fun k => ∃ a old new, k = .rmw a old new)
    (fun _ ⟨_, _, _, hk⟩ => by cases hk)
    (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk) noAtomicCode he ⟨_, _, _, rfl⟩

private theorem noThreadFenceCode :
    kernel.code.all (fun ins => !threadFenceOp ins.op) = true := by
  decide +kernel

theorem noThreadFence (hX : Consistent l kernel A m X) {i : EvId} {s : FenceSem} {scope : MbarScope}
    :
    ¬ X.ThreadFence i s scope := by
  rintro ⟨_, he⟩
  exact no_kind_of_code hX threadFenceOp (fun k => ∃ s scope, k = .fence s scope)
    (fun _ ⟨_, _, hk⟩ => by cases hk)
    (fun hf ⟨_, _, hk⟩ => fires_threadFence_op hf hk) noThreadFenceCode he ⟨_, _, rfl⟩

/-- Canonical polls and the absence of ordinary release or thread-fence events reduce
guarded synchronization to history prefixes ending in successful polls. -/
theorem guardedOfNoFaultBeforeSuccess (hX : Consistent l kernel A m X)
    (hf : ∀ mb (i j : Nat) (r w : MBarrier.Record AsyncCopy.Ref),
      (X.objects mb)[i]? = some r → (X.objects mb)[j]? = some w →
      w.reply.waited = some true → i ≤ j → r.fault = none) : SyncGuarded l kernel X where
  spin _ _ _ _ _ _ he := poll_canonical hX he
  noMemSync i j := ⟨noSynchronizesWith_of (fun _ _ _ _ he => noReleasingStore hX he)
    (fun _ _ _ _ _ he => (noAtomicEvent hX he).elim) i j,
    not_fenceSync_of_noFence (fun _ _ _ => noThreadFence hX) i j⟩
  noFault := hf

/-- Fault-free object histories suffice for guarded synchronization. -/
theorem guardedOfNoObjectFault (hX : Consistent l kernel A m X)
    (hf : ∀ mb r, r ∈ X.objects mb → r.fault = none) : SyncGuarded l kernel X :=
  guardedOfNoFaultBeforeSuccess hX
    (fun mb _ _ r _ hr _ _ _ => hf mb r (List.mem_of_getElem? hr))

theorem guardedOfTmaSafe (hX : Consistent l kernel A m X) (hSafe : ¬ TmaUnsafe l m X)
    : SyncGuarded l kernel X := by
  apply guardedOfNoObjectFault hX
  intro mb r hr
  cases hf : r.fault with
  | none => rfl
  | some f => exact (hSafe (.inl ⟨mb, r, hr, by simp [hf]⟩)).elim

end PTX.Kernels.TmlFa4Fwd.Proof
