-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Assumptions
public import Kernels.FlashKdaFwd.Spec
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.NotThreadFence
public import Lemmas.Flow.PollFacts
public import Lemmas.Order.GuardSnoc
public import Kernels.FlashKdaFwd.Proof.Top.Static

@[expose] public section

/-! # Three code facts the progress proof needs

No store of the kernel has release semantics, the kernel has no atomic instruction, and it has
no thread-level `fence` (its fences are the proxy fences and the mbarrier-initialization
fences). Each is one evaluated scan of the decoded program; they are the premises `noRelease`,
`noReleaseRmw` and `noFence` of `Progress.lean`. With the canonical polls of `Top/Static.lean`
they give the premise `guard` on every execution that is not unsafe (`syncGuarded`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {mem0 : Mem0} {A : List Assumption} {X : Execution}

set_option maxRecDepth 100000 in
private theorem noReleaseCode : kernel.code.all (fun ins => !releaseOp ins.op) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem noAtomicCode : kernel.code.all (fun ins => !atomicOp ins.op) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem noThreadFenceCode :
    kernel.code.all (fun ins => !threadFenceOp ins.op) = true := by
  decide +kernel

/-- No store of the kernel has release semantics. -/
theorem noReleasingStore (hX : Consistent L kernel A mem0 X) {i : EvId} {pc : Nat} {a : Acc}
    {bs : List Byte} (he : X.get i = some ⟨pc, .wr a bs⟩) : a.release = false := by
  rcases get_source hX he with ⟨_, hu⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hu
  have hOp : PTX.releaseOp ins.op = false := by
    simpa using List.all_eq_true.mp noReleaseCode ins (List.mem_of_getElem? hc)
  exact fires_write_release hf hOp rfl

/-- The kernel makes no atomic read-modify-write event. -/
theorem noAtomicEvent (hX : Consistent L kernel A mem0 X) {i : EvId} {pc : Nat} {a : Acc}
    {old : List (Option Byte)} {new : Option (List Byte)}
    (he : X.get i = some ⟨pc, .rmw a old new⟩) : False :=
  no_kind_of_code hX atomicOp (fun k => ∃ a old new, k = .rmw a old new)
    (fun _ ⟨_, _, _, hk⟩ => by cases hk)
    (fun hf ⟨_, _, _, hk⟩ => fires_rmw_op hf hk) noAtomicCode he ⟨_, _, _, rfl⟩

/-- The kernel makes no thread-level fence. -/
theorem noThreadFence (hX : Consistent L kernel A mem0 X) {i : EvId} {s : FenceSem}
    {scope : MbarScope} : ¬ X.ThreadFence i s scope := by
  rintro ⟨_, he⟩
  exact no_kind_of_code hX threadFenceOp (fun k => ∃ s scope, k = .fence s scope)
    (fun _ ⟨_, _, hk⟩ => by cases hk)
    (fun hf ⟨_, _, hk⟩ => fires_threadFence_op hf hk) noThreadFenceCode he ⟨_, _, rfl⟩

/-- **Synchronization is guarded** in every consistent execution that is not unsafe: successful
polls are at canonical spin loops (`Top.poll_canonical`), no memory order comes from a
release/acquire pair or a thread fence (the code has neither), and no mbarrier record faults
(a fault is undefined behaviour). -/
theorem syncGuarded (hX : Consistent L kernel Assumptions.all mem0 X)
    (hsafe : ¬ Unsafe L kernel Assumptions.all mem0 X) : SyncGuarded L kernel X where
  spin _ _ _ _ _ _ he := Top.poll_canonical hX he
  noMemSync e f := ⟨noSynchronizesWith_of (fun _ _ _ _ he => noReleasingStore hX he)
    (fun _ _ _ _ _ he => (noAtomicEvent hX he).elim) e f,
    not_fenceSync_of_noFence (fun _ _ _ => noThreadFence hX) e f⟩
  noFault m _ _ r _ hr _ _ _ := by
    cases hf : r.fault with
    | none => rfl
    | some f =>
      refine absurd ?_ hsafe
      exact .inr (.inr (.inr (.inr (.inr (.inl (.inl
        ⟨m, r, List.mem_of_getElem? hr, by simp [hf]⟩))))))

end PTX.Kernels.FlashKdaFwd.Proof.Progress
