-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingItems

@[expose] public section

/-! # The ready and free handoffs of a raw-buffer generation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing

open PTX AsyncCopy MBarrier PTX.Flow PTX.MbarRing

noncomputable section

local notation "full" => ready
local notation "empty" => free


/-- Successful ready polls acquire each gather of their own generation. -/
def GatherAcquires (L : Launch) (X : Execution) (cta issuer : Nat) : Prop :=
  ∀ {j p : Nat} {slot : Fin 2} {lane : Fin 128} {e : Event} {acq : Bool} {sc : MbarScope}
    (k : Fin 16), X.get (consumer L cta lane, j) = some e →
    e.kind = .wait (full L cta slot) p true acq sc →
    let m := full L cta slot
    let g := consumer L cta lane
    let u := PTX.Flow.okPolls m ((X.tr g).take j)
    AsyncObserved X (issuer, nthEv X (issuesTo m) issuer (16 * u + k.val))
      (.notify .load) (g, j) true .cta

private theorem gather_observation {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta g h j s p u : Nat} {slot : Fin 2} {i : EvId} {key : Item}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (h, j) = some ⟨s, .wait (full L cta slot) p true true .cta⟩)
    (hSF : (key, u) ∈ countedFull X (full L cta slot) g) (hkey : key.val ≠ 0)
    (hItem : itemFull X (full L cta slot) g key u = .async i (.notify .load))
    (hObs : MbarObserved X (.async i (.notify .load)) (.thread (h, j))) :
    AsyncObserved X i (.notify .load) (h, j) true .cta := by
  classical
  let m := full L cta slot
  obtain ⟨hPresent, w, n, aq, scope, hw, hObs, _⟩ := hObs
  obtain rfl := Ref.thread.inj hw
  obtain ⟨⟨_, _, he'⟩, hBefore⟩ := hObs
  obtain ⟨rfl, _, _, rfl, rfl⟩ := Kind.wait.inj (Event.mk.inj
    (Option.some.inj (he.symm.trans he'))).2
  obtain ⟨_, rec, hrec, hId, _, hAct⟩ := Finset.mem_filter.mp hSF
  have hRecId : rec.id = .async i (.notify .load) := hId.trans hItem
  have hrAct : rec.action = .completeTx 2304 := by
    rw [hAct, actionFull, ite_eq_right hkey]
  obtain ⟨_, g', j', event, a, p, d, q, hid, heIssue, hkIssue, hm, _, _, _, _, _, _⟩ :=
    actual_gather_record hpre hX hs hrec hrAct
  have hIssue := (Ref.async.inj (hid.symm.trans hRecId)).1
  rw [hIssue] at heIssue
  obtain ⟨o, ho, hn⟩ := id hPresent
  obtain ⟨_, si, hget⟩ := (hX.tensor i o ho).1
  have hSpec := (Kind.tensorIssue.inj
    ((Event.mk.inj (Option.some.inj (hget.symm.trans heIssue))).2.trans hkIssue)).2
  exact ⟨_, m, ⟨rfl, o, _, ho, ⟨si, hget⟩, congrArg TensorCopy.Spec.mbar hSpec |>.trans hm, hn⟩,
    ⟨⟨s, _, he⟩, hBefore⟩⟩


/-- A real acquire poll observes completion of each actual gather in its generation. -/
theorem gather_acquired {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta g j p : Nat} {slot : Fin 2} {lane : Fin 128} {e : Event} {acq : Bool} {sc : MbarScope}
    (k : Fin 16) (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hp : Issuer P L X cta g)
    (he : X.get (consumer L cta lane, j) = some e)
    (hk : e.kind = .wait (full L cta slot) p true acq sc) :
    let h := consumer L cta lane
    let m := full L cta slot
    let u := PTX.Flow.okPolls m ((X.tr h).take j)
    let issue := (g, nthEv X (issuesTo m) g (16 * u + k.val))
    AsyncObserved X issue (.notify .load) (h, j) true .cta := by
  classical
  let R := items (slot := slot) g hpre hX hs ht hp
  let m := full L cta slot
  let h := consumer L cta lane
  let u := PTX.Flow.okPolls m ((X.tr h).take j)
  let i := (g, nthEv X (issuesTo m) g (16 * u + k.val))
  let key : Item := ⟨k.val + 1, by have := k.isLt; omega⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨rfl, rfl, _⟩ := await_ready_source hpre hX (hs h hg) ht he hk
  obtain ⟨s, kind⟩ := e
  change kind = .wait m p true true .cta at hk
  subst kind
  have hPoll : MbarRing.Poll.nth X m h u = j := MbarRing.Poll.nth_eq he
  have hw : X.RefPresent (.thread (R.wF lane u)) := by
    change X.RefPresent (.thread (h, MbarRing.Poll.nth X m h u))
    rw [hPoll]
    exact ⟨_, he⟩
  have hn := MbarRing.Poll.nth_present.mp hw
  change u < PTX.Flow.okPolls m (X.tr h) at hn
  have hkey : key.val ≠ 0 := by simp [key]
  obtain ⟨hSF, hPhase⟩ := (R.content_full hX.depAcyclic hw).2 key
  change (key, u) ∈ countedFull X m g at hSF
  change phaseFull X m g (key, u) = Unit.obsOf X m h u at hPhase
  have hItem : itemFull X m g key u = .async i (.notify .load) := by
    rw [itemFull, ite_eq_right hkey, op_gather]
  have hObs := observed_full_item hpre hX hs ht hn hSF hPhase
  rw [hPoll, hItem] at hObs
  exact gather_observation hpre hX (fun _ hg => Machine.code_sound hpre hg) he hSF hkey hItem hObs

/-- The actual acquire orders completion of each gather of the acquired generation. -/
theorem actual_gather_acquired {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta g j p : Nat} {slot : Fin 2} {lane : Fin 128} {e : Event} {acq : Bool} {sc : MbarScope}
    (k : Fin 16) (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hWarp : warpOf L g = 5) (hp : Issuer P L X cta g)
    (he : X.get (consumer L cta lane, j) = some e)
    (hk : e.kind = .wait (full L cta slot) p true acq sc) :
    let h := consumer L cta lane
    let m := full L cta slot
    let u := PTX.Flow.okPolls m ((X.tr h).take j)
    let issue := (g, nthEv X (issuesTo m) g (16 * u + k.val))
    AsyncObserved X issue (.notify .load) (h, j) true .cta := by
  classical
  let R := actual_items (slot := slot) g hpre hX hs hWarp hp
  let m := full L cta slot
  let h := consumer L cta lane
  let u := PTX.Flow.okPolls m ((X.tr h).take j)
  let i := (g, nthEv X (issuesTo m) g (16 * u + k.val))
  let key : Item := ⟨k.val + 1, by have := k.isLt; omega⟩
  obtain ⟨rfl, rfl⟩ := RingSourceSites.actual_wait_acquire hX he hk
  obtain ⟨s, kind⟩ := e
  change kind = .wait m p true true .cta at hk
  subst kind
  have hPoll : MbarRing.Poll.nth X m h u = j := MbarRing.Poll.nth_eq he
  have hw : X.RefPresent (.thread (R.wF lane u)) := by
    change X.RefPresent (.thread (h, MbarRing.Poll.nth X m h u))
    rw [hPoll]
    exact ⟨_, he⟩
  have hn := MbarRing.Poll.nth_present.mp hw
  change u < PTX.Flow.okPolls m (X.tr h) at hn
  have hkey : key.val ≠ 0 := by simp [key]
  obtain ⟨hSF, hPhase⟩ := (R.content_full hX.depAcyclic hw).2 key
  change (key, u) ∈ countedFull X m g at hSF
  change phaseFull X m g (key, u) = Unit.obsOf X m h u at hPhase
  have hItem : itemFull X m g key u = .async i (.notify .load) := by
    rw [itemFull, ite_eq_right hkey, op_gather]
  have hObs := actual_observed_full_item hpre hX hs (consumer_ready_alternates lane hpre hX hs)
    hn hSF hPhase
  rw [hPoll, hItem] at hObs
  exact gather_observation hpre hX hs he hSF hkey hItem hObs


set_option maxRecDepth 4096 in
/-- The TMA producer's next acquire synchronizes with each dequantizer release of the preceding
use of the same raw buffer. -/
theorem free_release_sync {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta g j p u : Nat} {slot : Fin 2} {e : Event} {acq : Bool} {sc : MbarScope}
    (lane : Fin 128) (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hp : Issuer P L X cta g)
    (he : X.get (g, j) = some e) (hk : e.kind = .wait (empty L cta slot) p true acq sc)
    (hu : PTX.Flow.okPolls (empty L cta slot) ((X.tr g).take j) = u + 1) :
    MbarRing.Syncs L X (Unit.it X (empty L cta slot) (consumer L cta) lane u)
      (g, j) (empty L cta slot) := by
  let R := items (slot := slot) g hpre hX hs ht hp
  let m := empty L cta slot
  let E := free_obj hpre hX hs ht (cta := cta) (slot := slot)
  have hg := Frame.lt_of_get hX he
  obtain ⟨rfl, rfl, hc, _⟩ := reuse_source hpre hX (hs g hg) ht he hk
  obtain ⟨site, kind⟩ := e
  change kind = .wait m p true true .cta at hk
  subst kind
  have hPoll : MbarRing.Poll.nth X m g (u + 1) = j := by rw [← hu, MbarRing.Poll.nth_eq he]
  have hw : X.RefPresent (.thread (R.wE 0 (u + 1))) := by
    change X.RefPresent (.thread (g, MbarRing.Poll.nth X m g (u + 1)))
    rw [hPoll]
    exact ⟨_, he⟩
  have hn := MbarRing.Poll.nth_present.mp hw
  change u + 1 < PTX.Flow.okPolls m (X.tr g) at hn
  obtain ⟨hS, hPhase⟩ := (R.content_empty hX.depAcyclic hw).2 lane
  change (lane, u) ∈ Unit.S X m (consumer L cta) at hS
  change Unit.ph X m (consumer L cta) (lane, u) = Unit.obsOf X m g (u + 1) at hPhase
  have hBefore := E.ubw hX (by omega : 1 ≤ u + 1) hn hS hPhase
  rw [hPoll] at hBefore
  obtain ⟨_, ⟨_, _, he'⟩, _⟩ := E.S_rec hS
  have hh := Frame.lt_of_get hX he'
  have hwcta : ctaOf L (consumer L cta lane) = cta := by
    have hLane := lane.isLt
    simp only [consumer, ctaOf, hpre.block]
    omega
  exact (Unit.Ring.syncs E hS he hBefore ⟨hh, hg, hwcta.trans hc.symm⟩).2


set_option maxRecDepth 4096 in
/-- The actual TMA reuse wait observes each dequantizer's release of the old raw generation. -/
theorem actual_free_release_sync {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta g j p u : Nat} {slot : Fin 2} {e : Event} {acq : Bool} {sc : MbarScope}
    (lane : Fin 128) (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hWarp : warpOf L g = 5) (hp : Issuer P L X cta g) (hCta : ctaOf L g = cta)
    (he : X.get (g, j) = some e) (hk : e.kind = .wait (empty L cta slot) p true acq sc)
    (hu : PTX.Flow.okPolls (empty L cta slot) ((X.tr g).take j) = u + 1) :
    MbarRing.Syncs L X (Unit.it X (empty L cta slot) (consumer L cta) lane u)
      (g, j) (empty L cta slot) := by
  let R := actual_items (slot := slot) g hpre hX hs hWarp hp
  let m := empty L cta slot
  let E := actual_free_history hpre hX hs (cta := cta) (slot := slot)
  obtain ⟨rfl, rfl⟩ := RingSourceSites.actual_wait_acquire hX he hk
  obtain ⟨site, kind⟩ := e
  change kind = .wait m p true true .cta at hk
  subst kind
  have hPoll : MbarRing.Poll.nth X m g (u + 1) = j := by rw [← hu, MbarRing.Poll.nth_eq he]
  have hw : X.RefPresent (.thread (R.wE 0 (u + 1))) := by
    change X.RefPresent (.thread (g, MbarRing.Poll.nth X m g (u + 1)))
    rw [hPoll]
    exact ⟨_, he⟩
  obtain ⟨hS, hPhase⟩ := (R.content_empty hX.depAcyclic hw).2 lane
  have hn := MbarRing.Poll.nth_present.mp hw
  have hBefore := E.ubw hX (by decide) (tma_free_alternates hpre hX hs hWarp)
    (by omega : 1 ≤ u + 1) hn hS hPhase
  rw [hPoll] at hBefore
  obtain ⟨_, ⟨tag, sc, hRelease⟩, _⟩ := E.S_rec hS
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX hRelease
  have hSame : SameCta L (consumer L cta lane) g :=
    ⟨hh, hg, (actual_consumer_geometry hpre cta lane).1.trans hCta.symm⟩
  exact ⟨sc, ⟨0, 1, tag, hRelease⟩, .cta, ⟨⟨site, p, he⟩, hBefore⟩,
    Unit.Gate.scopesMeet hSame sc .cta⟩


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing
