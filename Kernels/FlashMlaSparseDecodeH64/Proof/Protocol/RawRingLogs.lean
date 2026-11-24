-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingSources
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingInitialized
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaRawTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRawActualArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCommitOrigins
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # Record sources and initialization of the raw ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing

open PTX MBarrier AsyncCopy PTX.MbarRing PTX.Flow MachineTracking

/-- The dequantizer's 128 lanes in a CTA. -/
def consumer (L : Launch) (cta : Nat) (lane : Fin 128) : Nat := cta * L.block + 256 + lane.val

theorem consumer_inj (L : Launch) (cta : Nat) : Function.Injective (consumer L cta) := by
  intro a b h
  apply Fin.ext
  exact Nat.add_left_cancel h

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- An actual warpgroup-two thread has a CTA-local dequantizer lane. -/
theorem consumer_of_wg2 (hpre : Pre P L mem0) {g cta : Nat} (hc : ctaOf L g = cta)
    (hw : wgOf L g = 2) : ∃ lane, g = consumer L cta lane := by
  simp only [ctaOf, hpre.block] at hc
  simp only [wgOf, tidOf_eq hpre] at hw
  refine ⟨⟨g % 128, Nat.mod_lt _ (by decide)⟩, ?_⟩
  simp only [consumer, hpre.block]
  omega

private theorem raw_range {L : Launch} {cta : Nat} {slot : Fin 2} {m : Loc}
    (hm : m = ready L cta slot ∨ m = free L cta slot) :
    L.sharedBase + 222808 ≤ m.addr ∧ m.addr ≤ L.sharedBase + 222832 := by
  have hs := slot.isLt
  rcases hm with rfl | rfl
  · simp only [ready, Wg2.rawReadyOff]
    omega
  · simp only [free, Wg2.rawFreeOff]
    omega

private theorem no_commit {X : Execution} {cta : Nat} {slot : Fin 2} {i : EvId} {e : Event}
    {sp : TcCommit.Spec} {rank : Fin 16} {m : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hm : m = ready L cta slot ∨ m = free L cta slot) (he : X.get i = some e)
    (hk : e.kind = .tc (.commit sp)) (hTarget : TcCommit.target sp rank = some m) :
    False := by
  rcases i with ⟨g, i⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, hfire⟩ := actual_commit_fired hpre hX hs he hk
  have h := raw_range hm
  rcases RingCommitEvents.commit_address hpre hg hfire hk hTarget with ha | ⟨b, ha⟩ | ⟨b, ha⟩
  all_goals omega

private theorem gather_on_raw {X : Execution} {g i a cta : Nat} {e : Event} {sp : TensorCopy.Spec}
    {m : Loc} {slot : Fin 2} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hm : m = ready L cta slot ∨ m = free L cta slot) (he : X.get (g, i) = some e)
    (hk : e.kind = .tensorIssue a sp) (hb : sp.mbar = m) :
    m = ready L cta slot ∧ ctaOf L g = cta ∧ TensorTransfer.bytes sp.descriptor = 2304 ∧
    ∃ d k, d.site = .issue k ∧ d.block % 2 = slot.val ∧
      sp.sharedBase = ⟨.shared, cta, L.sharedBase + Wg1Tma.issueDst slot.val k.val⟩ ∧
      a = P.param1Base + Wg1Tma.kvOff d ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) := by
  have hg := Frame.lt_of_get hX he
  have hFollow := actual_tensor_issue_followed hpre hX hs he hk
  obtain ⟨d, _, hst, hfire⟩ := RingSourceSites.fired_at_followed hX (hs g hg).machine hFollow he (by
    intro f hf
    rw [hk] at hf
    cases hf)
  have haddr := raw_range hm
  rcases RingTensorEvents.issue_source hpre hfire hk with
    hQ | ⟨q, k, rfl, hsite, hmap, hdst, hraw, hn⟩
  · have ha := congrArg Loc.addr (hb.symm.trans hQ)
    change m.addr = L.sharedBase + 222776 at ha
    omega
  · have hh := hb.symm.trans hraw
    rcases hm with h | h
    · have hc := congrArg Loc.cta (h.symm.trans hh)
      have hp := congrArg Loc.addr (h.symm.trans hh)
      change cta = ctaOf L g at hc
      change L.sharedBase + (222808 + 8 * slot.val) =
        L.sharedBase + (222808 + 8 * (q.block % 2)) at hp
      have hslot : q.block % 2 = slot.val := by omega
      rw [← hc, hslot] at hdst
      exact ⟨h, hc.symm, hn, q, k, hsite, hslot, hdst, hmap, hst⟩
    · have ha := congrArg Loc.addr (h.symm.trans hh)
      change L.sharedBase + (222824 + 8 * slot.val) =
        L.sharedBase + (222808 + 8 * (q.block % 2)) at ha
      omega

/-- The notification record of a ready slot comes from an actual gather of that raw buffer. -/
theorem actual_gather_record {X : Execution} {cta n : Nat} {slot : Fin 2} {r : Record Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hr : r ∈ X.objects (ready L cta slot))
    (ha : r.action = .completeTx n) :
    n = 2304 ∧ ∃ g i e a sp d k, r.id = .async (g, i) (.notify .load) ∧
      X.get (g, i) = some e ∧ e.kind = .tensorIssue a sp ∧ sp.mbar = ready L cta slot ∧
      ctaOf L g = cta ∧ d.site = .issue k ∧ d.block % 2 = slot.val ∧
      sp.sharedBase = ⟨.shared, cta, L.sharedBase + Wg1Tma.issueDst slot.val k.val⟩ ∧
      a = P.param1Base + Wg1Tma.kvOff d ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) := by
  obtain ⟨⟨g, i⟩, e, a, sp, hid, he, hk, hm, hn⟩ := object_completion_source hX hr ha
  obtain ⟨_, hc, hn', d, k, hsite, hslot, hdst, hmap, hst⟩ :=
    gather_on_raw hpre hX hs (.inl rfl) he hk hm
  exact ⟨hn.symm.trans hn', g, i, e, a, sp, d, k, hid, he, hk, hm, hc, hsite,
    hslot, hdst, hmap, hst⟩

private theorem no_free_completion {X : Execution} {cta n : Nat} {slot : Fin 2} {r : Record Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hr : r ∈ X.objects (free L cta slot))
    (ha : r.action = .completeTx n) : False := by
  obtain ⟨⟨g, i⟩, e, a, sp, _, he, hk, hm, _⟩ := object_completion_source hX hr ha
  have h := (gather_on_raw hpre hX hs (.inr rfl) he hk hm).1
  have haddr := congrArg Loc.addr h
  change L.sharedBase + (222824 + 8 * slot.val) =
    L.sharedBase + (222808 + 8 * slot.val) at haddr
  omega

/-- The raw-free object contains only initialization, thread polls and unit dequantizer arrivals. -/
theorem actual_free_sources {X : Execution} {cta : Nat} {slot : Fin 2} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    ∀ r ∈ X.objects (free L cta slot),
      Unit.Source X (free L cta slot) (fun g => ∃ lane, g = consumer L cta lane) r := by
  intro r hr
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact .init ha
  | wait hid he ha => exact .poll hid he ha
  | @arrive g i _ _ _ _ _ hid he ha =>
    obtain ⟨rfl, rfl, rfl, _, hc, hw, _⟩ := actual_raw_free_arrive hpre hX hs he rfl
    exact .arrive hid (consumer_of_wg2 hpre hc hw) he ha
  | inval _ _ ha => exact ((objects_single_lifetime hX _) r hr ha).elim
  | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
  | tensor _ _ _ ha | bulk _ _ _ _ ha | clc _ _ _ _ ha =>
    exact (no_free_completion hpre hX hs hr ha).elim
  | commit _ he hTarget _ =>
    exact (no_commit hpre hX hs (.inr rfl) he rfl hTarget).elim

/-- Every actual ready arrival expects one unit and precisely sixteen gathers' worth of bytes. -/
theorem actual_ready_arrival_record {X : Execution} {cta n tx : Nat} {slot : Fin 2} {r : Record Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hr : r ∈ X.objects (ready L cta slot))
    (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 36864 ∧ ∃ g i e d, r.id = .thread (g, i) ∧ X.get (g, i) = some e ∧
      e.kind = .arrive (ready L cta slot) 36864 1 true .cta ∧ ctaOf L g = cta ∧
      d.site = .rawReady ∧ d.block % 2 = slot.val ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) := by
  cases record_source hX.tma.2.2.1 hr with
  | @arrive g i _ _ _ _ _ hid he ha' =>
    obtain ⟨rfl, rfl⟩ := Action.arrive.inj (ha.symm.trans ha')
    obtain ⟨rfl, rfl, rfl, rfl, hc, d, hslot, hsite, hst⟩ :=
      actual_raw_ready_arrive hpre hX hs he rfl
    exact ⟨rfl, rfl, g, i, _, d, hid, he, rfl, hc, hsite, hslot, hst⟩
  | commit _ he hTarget _ => exact (no_commit hpre hX hs (.inl rfl) he rfl hTarget).elim
  | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
  | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | increment _ _ ha' | tensor _ _ _ ha'
  | bulk _ _ _ _ ha' | clc _ _ _ _ ha' =>
    rw [ha] at ha'
    cases ha'

/-- The gather record in a fully followed execution. -/
theorem gather_record {X : Execution} {cta n : Nat} {slot : Fin 2} {r : Record Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (hr : r ∈ X.objects (ready L cta slot))
    (ha : r.action = .completeTx n) :
    n = 2304 ∧ ∃ g i e a sp d k, r.id = .async (g, i) (.notify .load) ∧
      X.get (g, i) = some e ∧ e.kind = .tensorIssue a sp ∧ sp.mbar = ready L cta slot ∧
      ctaOf L g = cta ∧ d.site = .issue k ∧ d.block % 2 = slot.val ∧
      sp.sharedBase = ⟨.shared, cta, L.sharedBase + Wg1Tma.issueDst slot.val k.val⟩ ∧
      a = P.param1Base + Wg1Tma.kvOff d ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) :=
  actual_gather_record hpre hX (fun _ hg => Machine.code_sound hpre hg) hr ha

/-- The raw-free history in a fully followed execution. -/
theorem free_sources {X : Execution} {cta : Nat} {slot : Fin 2} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) :
    ∀ r ∈ X.objects (free L cta slot),
      Unit.Source X (free L cta slot) (fun g => ∃ lane, g = consumer L cta lane) r :=
  actual_free_sources hpre hX (fun _ hg => Machine.code_sound hpre hg)

/-- The raw-ready arrival record in a fully followed execution. -/
theorem ready_arrival_record {X : Execution} {cta n tx : Nat} {slot : Fin 2} {r : Record Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (hr : r ∈ X.objects (ready L cta slot))
    (ha : r.action = .arrive n tx) :
    n = 1 ∧ tx = 36864 ∧ ∃ g i e d, r.id = .thread (g, i) ∧ X.get (g, i) = some e ∧
      e.kind = .arrive (ready L cta slot) 36864 1 true .cta ∧ ctaOf L g = cta ∧
      d.site = .rawReady ∧ d.block % 2 = slot.val ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) :=
  actual_ready_arrival_record hpre hX (fun _ hg => Machine.code_sound hpre hg) hr ha

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing
