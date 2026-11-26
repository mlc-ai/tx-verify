-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.UnitGate
public import Lemmas.Order.OrderWaits
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Kernel.ExitChain

@[expose] public section

/-! # From "a poll observed a tensor load's completion" to orders at a byte

A proof tool, generic over the kernel. The ring lemmas conclude that a successful poll `w` of an
mbarrier observed the completion notification of a tensor load issued at `i`
(`AsyncCopy.WaitObserves X (.async i (.notify .load)) w m acq sc`; e.g.
`MbarRing.TmaSized.Stage.copy_observed`). The memory model orders the load's byte writes before
other accesses through that observation (MEM-OBSERVED-COMPLETION, MEM-MODEL-CAUSALITY). This
file makes the three steps once:

* `WaitObserves.load_notified`, `WaitObserves.load_mbar`: the load has a notified observation,
  and its completion barrier is the polled one;
* `WaitObserves.asyncFinished`: for an acquiring poll of a thread of the issuer's CTA, each
  byte write of the load is finished at the poll (`AsyncFinished`);
* `WaitObserves.write_before_thread`: the write is visible to a thread event that the poll
  happens before (`write_before_later` for a later event of the polling thread itself);
* `WaitObserves.write_before_async`: the write is visible to every part of an asynchronous
  operation of the same CTA whose issue the poll happens before (`AsyncBefore`, one link of
  `AsyncChain`); `write_before_later_async` for an issue by the polling thread.

For the shared-memory lifetime rule (`SharedLifetimeUnsafe`: a use of a CTA's shared memory must
be finished before an exit of one of the CTA's threads once all of them exited):

* `WaitObserves.notify_finished`: a load whose notification was observed by a poll of a thread
  that ends with an exit is finished (`SharedFinished`), the poll being the head of a canonical
  spin loop so that the exit depends on its return;
* `load_write_finished`: so is each byte write of the load, which precedes the notification. -/

namespace PTX.AsyncCopy

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The record of a tensor load's notification on an object names the load's issue, whose
completion barrier is the object. -/
theorem WaitObserves.load_mbar (hX : Consistent L K A mem0 X) {i w : EvId} {m : Loc}
    {acq : Bool} {sc : MbarScope} (h : WaitObserves X (.async i (.notify .load)) w m acq sc) :
    ∃ pc a sp, X.get i = some ⟨pc, .tensorIssue a sp⟩ ∧ sp.mbar = m := by
  obtain ⟨_, _, r, _, _, hr, hid, -⟩ := h.2
  cases record_source hX.tma.2.2.1 (List.mem_of_getElem? hr) with
  | tensor hid' he hm _ =>
    rw [hid] at hid'
    cases hid'
    exact ⟨_, _, _, he, hm⟩
  | init hid' _ _ | inval hid' _ _ | arrive hid' _ _ | wait hid' _ _ | increment hid' _ _
  | arriveOn hid' _ _ _ _ | bulk hid' _ _ _ _ | commit hid' _ _ _ | clc hid' _ _ _ _ =>
    rw [hid] at hid'
    cases hid'

/-- **A wait that observed a load's notification: the load has its notified observation.** -/
theorem WaitObserves.load_notified (hX : Consistent L K A mem0 X) {i w : EvId} {m : Loc}
    {acq : Bool} {sc : MbarScope} (h : WaitObserves X (.async i (.notify .load)) w m acq sc) :
    ∃ o, X.tensor i = some o ∧ o.effects.notified = true := by
  obtain ⟨_, _, r, _, _, hr, hid, -⟩ := h.2
  have hp := object_record_present hX.tma (List.mem_of_getElem? hr)
  rw [hid] at hp
  exact hp

/-- **The wait observed every byte write of the load.** -/
theorem WaitObserves.write_observed (hX : Consistent L K A mem0 X) {i w : EvId} {m : Loc}
    {acq : Bool} {sc : MbarScope} (h : WaitObserves X (.async i (.notify .load)) w m acq sc)
    (x y z : Nat) : AsyncObserved X i (.write (.load x y z)) w acq sc := by
  obtain ⟨o, ho, hn⟩ := h.load_notified hX
  obtain ⟨pc, a, sp, he, hm⟩ := h.load_mbar hX
  obtain ⟨⟨addr, pc', he'⟩, -⟩ := hX.tensor i o ho
  have hsp : o.spec = sp := by
    rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at he'
    exact he'.2.2.symm
  exact ⟨_, m, ⟨rfl, o, addr, ho, ⟨pc', he'⟩, by rw [hsp]; exact hm, hn⟩, h⟩

/-- **For an acquiring poll of a thread of the issuer's CTA, each byte write of the load is
finished at the poll.** -/
theorem WaitObserves.asyncFinished (hX : Consistent L K A mem0 X) {i w : EvId} {m : Loc}
    {sc : MbarScope} (h : WaitObserves X (.async i (.notify .load)) w m true sc)
    (hsame : SameCta L i.1 w.1) (x y z : Nat) :
    AsyncFinished L X i (.write (.load x y z)) w :=
  .inr ⟨sc, h.write_observed hX x y z, MbarRing.Unit.Gate.scopesMeet hsame .cluster sc⟩

/-- **The load's write is visible to a thread event the poll happens before.** -/
theorem WaitObserves.write_before_thread (hX : Consistent L K A mem0 X) {i w f : EvId}
    {m : Loc} {sc : MbarScope} (h : WaitObserves X (.async i (.notify .load)) w m true sc)
    (hsame : SameCta L i.1 w.1) {x y z : Nat} {l : Loc}
    (hcov : AsyncCovers X i (.write (.load x y z)) l) (hwf : baseCausality L X w f) :
    modelCausality L X l (.async i (.write (.load x y z))) (.thread f) :=
  ⟨hcov, w, h.asyncFinished hX hsame x y z, .inl hwf⟩

/-- A later event of the thread of a successful poll follows it in base causality. -/
theorem WaitObserves.baseCausality_later {x : Ref} {w : EvId} {m : Loc} {acq : Bool}
    {sc : MbarScope} (h : WaitObserves X x w m acq sc) {j : Nat} (hj : w.2 < j)
    (hlen : j < (X.tr w.1).length) : baseCausality L X w (w.1, j) := by
  obtain ⟨pc, par, hw⟩ := h.1
  exact .single (.inl (po_of_source_not_access rfl hj hlen (by rw [hw]; rfl)))

/-- **The load's write is visible to a later event of the polling thread.** -/
theorem WaitObserves.write_before_later (hX : Consistent L K A mem0 X) {i w : EvId}
    {m : Loc} {sc : MbarScope} (h : WaitObserves X (.async i (.notify .load)) w m true sc)
    (hsame : SameCta L i.1 w.1) {x y z : Nat} {l : Loc}
    (hcov : AsyncCovers X i (.write (.load x y z)) l) {j : Nat} (hj : w.2 < j)
    (hlen : j < (X.tr w.1).length) :
    modelCausality L X l (.async i (.write (.load x y z))) (.thread (w.1, j)) :=
  h.write_before_thread hX hsame hcov (h.baseCausality_later hj hlen)

/-- **The load's write is visible to every part of an asynchronous operation of the same CTA
whose issue the poll happens before.** -/
theorem WaitObserves.write_before_async (hX : Consistent L K A mem0 X) {i w j : EvId}
    {m : Loc} {sc : MbarScope} (h : WaitObserves X (.async i (.notify .load)) w m true sc)
    (hsame : SameCta L i.1 w.1) (hij : SameCta L i.1 j.1) {x y z : Nat} {l : Loc} {q : Part}
    (hcov : AsyncCovers X i (.write (.load x y z)) l) (hcov' : AsyncCovers X j q l)
    (hwj : baseCausality L X w j) :
    modelCausality L X l (.async i (.write (.load x y z))) (.async j q) :=
  ⟨.inl hij, .direct ⟨hcov, hcov', .inl ⟨w, h.asyncFinished hX hsame x y z, hwj⟩⟩⟩

/-- **The load's write is visible to every part of an asynchronous operation the polling thread
issues later.** -/
theorem WaitObserves.write_before_later_async (hX : Consistent L K A mem0 X) {i w : EvId}
    {m : Loc} {sc : MbarScope} (h : WaitObserves X (.async i (.notify .load)) w m true sc)
    (hsame : SameCta L i.1 w.1) {x y z : Nat} {l : Loc} {q : Part} {j : Nat}
    (hcov : AsyncCovers X i (.write (.load x y z)) l)
    (hcov' : AsyncCovers X (w.1, j) q l) (hj : w.2 < j) (hlen : j < (X.tr w.1).length) :
    modelCausality L X l (.async i (.write (.load x y z))) (.async (w.1, j) q) :=
  h.write_before_async hX (j := (w.1, j)) hsame hsame hcov hcov'
    (h.baseCausality_later hj hlen)

/-- **A load whose notification a poll observed is finished once the polling thread exits.**
`hspin`: the poll heads a canonical spin loop (the loop `poll; @p bra exit; bra poll`), so
every later instruction of the thread, its exit included, depends on the poll's return. -/
theorem WaitObserves.notify_finished (hX : Consistent L K A mem0 X) {i w : EvId} {m : Loc}
    {acq : Bool} {sc : MbarScope} (h : WaitObserves X (.async i (.notify .load)) w m acq sc)
    (hspin : ∀ pc par, X.get w = some ⟨pc, .wait m par true acq sc⟩ →
      ∃ ex, K.CanonicalSpin pc ex)
    {c pcx : Nat} (hg : w.1 < L.threads) (hc : w.1 / L.block = c)
    (hexit : X.get (w.1, (X.tr w.1).length - 1) = some ⟨pcx, .exit⟩) :
    SharedFinished L K A X (.async i (.notify .load)) c := by
  obtain ⟨pc, par, hw⟩ := h.1
  obtain ⟨ex, hs⟩ := hspin pc par hw
  have hlen : (X.tr w.1).length - 1 < (X.tr w.1).length :=
    (List.getElem?_eq_some_iff.mp hexit).1
  have hlt : w.2 < (X.tr w.1).length - 1 := by
    have h1 : w.2 < (X.tr w.1).length := (List.getElem?_eq_some_iff.mp hw).1
    rcases Nat.lt_or_eq_of_le (show w.2 ≤ (X.tr w.1).length - 1 by omega) with h2 | h2
    · exact h2
    · have h3 : X.get w = X.get (w.1, (X.tr w.1).length - 1) := by rw [← h2]
      rw [hw, hexit] at h3
      cases h3
  have hres : Resumes K X w (w.1, (X.tr w.1).length - 1) := Resumes.of_spin hw hs rfl hlt hlen
  exact SharedFinished.of_completedBefore (finish := (w.1, (X.tr w.1).length - 1))
    (h.load_notified hX) ⟨hg, hc, pcx, hexit⟩
    (CompletedBefore.of_before h.before (.single (DepStep.of_resumes L hres)))

/-- **Each byte write of a finished load is finished**: the write precedes the load's
notification. -/
theorem load_write_finished (hX : Consistent L K A mem0 X) {i : EvId} {a c : Nat}
    {s : TensorCopy.Spec} (hi : X.TensorIssue i a s)
    (hfin : SharedFinished L K A X (.async i (.notify .load)) c) {x y k : Nat}
    (hsl : (TensorTransfer.slotAt s.descriptor x y k).isSome) :
    SharedFinished L K A X (.async i (.write (.load x y k))) c := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨o, hto, hnot⟩ := hfin.1
  obtain ⟨slot, hslot⟩ := Option.isSome_iff_exists.mp hsl
  have hspec : o.spec = s := by
    obtain ⟨a', pc', hio⟩ := (hX.effectValidity.tensor i o hto).1
    rw [he] at hio
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hio
    exact hio.2.2.symm
  subst hspec
  obtain ⟨v, hv⟩ := (hX.effectValidity.tensor i o hto).2.1.complete hnot slot
  have hwp : X.AsyncPresent i (.write (.load x y k)) := ⟨o, slot, v, hto, hslot, hv⟩
  exact SharedFinished.of_stage (j := i) (q := .notify .load) hwp
    (.inr ⟨rfl, rfl, rfl, rfl, hwp, o, hto, hnot⟩) hfin

end PTX.AsyncCopy
