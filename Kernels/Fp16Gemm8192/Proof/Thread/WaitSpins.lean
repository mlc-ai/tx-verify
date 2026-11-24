-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked
public import Lemmas.Flow.Bound
public import Lemmas.Flow.PollFacts
public import Lemmas.Flow.WaitLoopPcs
public import Lemmas.Snoc.ObjectAppend
public import Lemmas.Snoc.SnocObjectOrder

@[expose] public section

/-! # The kernel's polls spin and its stores do not release

Every `mbarrier.try_wait` of the kernel is at a listed position (`Flow.mbarWait`), and each
listed poll heads a wait loop `L: mbarrier.try_wait p, [b], par; @p bra DONE; bra L;` that no branch
enters and whose branch alone reads `p` (`Kernel.waitLoopPcs`, decided on the code). So every
successful wait is the poll of a canonical spin (`wait_spins`, by
`Kernel.canonicalSpin_of_waitLoopPcs`). The kernel has no `releaseOp` instruction (decided on the
code), so no write event of a thread releases (`write_no_release`, by `Frame.write_no_release`)
and no base causality edge is a release/acquire memory read. With the fault freedom of the
objects' records this guards the kernel's synchronization (`SyncGuarded`); appending a
non-writing event, or a non-poll object record, keeps it (`SyncGuarded.snoc`,
`SyncGuarded.snocObject`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- Every poll of the kernel is at a listed position (decided on the code). -/
theorem kernel_poll_pcs : OpPcsFast kernel.code pollOp Flow.mbarWait.toList = true := by
  decide +kernel

/-- Every listed poll heads a wait loop that no branch enters, and its predicate is read nowhere
but in the loop's branch (decided on the code). -/
theorem kernel_wait_loops : kernel.waitLoopPcs Flow.mbarWait.toList = true := by
  decide +kernel

/-- **Every successful wait of a thread is the poll of a canonical spin**: it fires from a poll
of the code, which is listed and heads a wait loop. -/
theorem wait_spins {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k pc : Nat} {m : Loc}
    {p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait m p true acq sc⟩) :
    ∃ exit, kernel.CanonicalSpin pc exit := by
  obtain ⟨d, hσ⟩ := Frame.event_state (fun _ => sound hpre) hX (tracked hpre hX) he
    (fun _ _ h => by cases h)
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hpc := EventFrame.fires_source_pc hf
  simp only at hpc
  subst hpc
  by_cases hw : ∃ q b off par a s, ins.op = .mbarWait q b off par a s
  · obtain ⟨q, b, off, par, a, s, hop⟩ := hw
    exact Kernel.canonicalSpin_of_waitLoopPcs kernel_poll_pcs kernel_wait_loops hc hop
  · push Not at hw
    exact absurd rfl (fires_notWait (eventTmpl_notWait hw) hf m p true acq sc)

/-- The kernel has no `releaseOp` instruction (decided on the code). -/
theorem kernel_no_releaseOp : kernel.code.all (fun ins => !releaseOp ins.op) = true := by
  decide +kernel

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- No write event of a thread has release semantics. -/
theorem write_no_release (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte} (he : X.get e = some ⟨pc, .wr a bs⟩) :
    a.release = false :=
  Frame.write_no_release (fun _ => sound hpre) hX (tracked hpre hX) kernel_no_releaseOp he

end
end PTX.Kernels.Fp16Gemm8192.Proof
