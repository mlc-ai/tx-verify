-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingInitialized
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents

@[expose] public section

/-! # Checked record sources of the index ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing

open PTX AsyncCopy MBarrier PTX.MbarRing
open IndexRingThreads

variable {P : Params} {L : Launch}

private theorem no_commit {mem0 : Mem0} {X : Execution} {cta : Nat} {slot : Fin 4} {i : EvId}
    {e : Event} {sp : TcCommit.Spec} {rank : Fin 16} {m : Loc} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hm : m = ready L cta slot ∨ m = free L cta slot) (he : X.get i = some e)
    (hk : e.kind = .tc (.commit sp)) (hTarget : TcCommit.target sp rank = some m) :
    False := by
  rcases i with ⟨g, i⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, hfire⟩ := RingSourceSites.fired_from_trace hX (hs g hg) ht he (by
    intro f hf
    rw [hk] at hf
    cases hf)
  have h := ring_addr_range hm
  rcases RingCommitEvents.commit_address hpre hg hfire hk hTarget with ha | ⟨b, ha⟩ | ⟨b, ha⟩
  all_goals omega

private theorem no_completion {mem0 : Mem0} {X : Execution} {cta n : Nat} {slot : Fin 4} {m : Loc}
    {r : Record Ref} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hm : m = ready L cta slot ∨ m = free L cta slot) (hr : r ∈ X.objects m)
    (ha : r.action = .completeTx n) : False := by
  obtain ⟨⟨g, i⟩, e, a, sp, _, he, hk, hm', _⟩ := object_completion_source hX hr ha
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, hfire⟩ := RingSourceSites.fired_from_trace hX (hs g hg) ht he (by
    intro f hf
    rw [hk] at hf
    cases hf)
  have hbound := ring_addr_range hm
  rcases RingTensorEvents.issue_source hpre hfire hk with hQ | ⟨d, _, _, _, _, _, hraw, _⟩
  · have haddr := congrArg Loc.addr (hm'.symm.trans hQ)
    change m.addr = L.sharedBase + 222776 at haddr
    omega
  · have haddr := congrArg Loc.addr (hm'.symm.trans hraw)
    change m.addr = L.sharedBase + (222808 + 8 * (d.block % 2)) at haddr
    omega

/-- A trace determines the TMA lane that can release this CTA's index slots. -/
def TmaConsumer (P : Params) (L : Launch) (X : Execution) (cta : Nat) (lane : Fin 32) : Prop :=
  ∀ {g i : Nat} {e : Event} {d : Wg1Tma.D}, X.get (g, i) = some e →
    ctaOf L g = cta → d.site = .coordFree →
    Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) → laneOf L g = lane.val

/-- The ready log comprises thread polls and warp 7's unit releases after initialization. -/
theorem ready_sources {mem0 : Mem0} {X : Execution} {cta : Nat} {slot : Fin 4} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    :
    ∀ r ∈ X.objects (ready L cta slot),
      Unit.Source X (ready L cta slot) (fun g => ∃ lane, g = producerThread L cta lane) r := by
  intro r hr
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact .init ha
  | wait hid he ha => exact .poll hid he ha
  | @arrive g i _ _ _ _ _ hid he ha =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨⟨hc, d, _, _, hst⟩, rfl, rfl, rfl, _⟩ :=
      publish_source hpre hX (hs g hg) ht he rfl
    have hw := RingRoleGeometry.of_trace hX hg (hs g hg) hst
    exact .arrive hid (producer_of_warp hpre hc hw) he ha
  | inval _ _ ha => exact ((objects_single_lifetime hX _) r hr ha).elim
  | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
  | tensor _ _ _ ha | bulk _ _ _ _ ha | clc _ _ _ _ ha =>
    exact (no_completion hpre hX hs ht (.inl rfl) hr ha).elim
  | commit _ he hTarget _ => exact (no_commit hpre hX hs ht (.inl rfl) he rfl hTarget).elim

/-- The free log comprises warpgroup zero's releases and the selected TMA lane's release. -/
theorem free_sources {mem0 : Mem0} {X : Execution} {cta : Nat} {slot : Fin 4} {lane : Fin 32}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hLane : TmaConsumer P L X cta lane) :
    ∀ r ∈ X.objects (free L cta slot),
      Unit.Source X (free L cta slot) (fun g => ∃ q, g = consumerThread L cta lane q) r := by
  intro r hr
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact .init ha
  | wait hid he ha => exact .poll hid he ha
  | @arrive g i _ _ _ _ _ hid he ha =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨⟨hc, hrole⟩, rfl, rfl, rfl, _⟩ :=
      release_source hpre hX (hs g hg) ht he rfl
    rcases hrole with ⟨d, _, _, hst⟩ | ⟨d, _, hd, hst⟩
    · have hw := RingRoleGeometry.of_trace hX hg (hs g hg) hst
      obtain ⟨q, _, hq⟩ := consumer_of_wg0 hpre hc hw lane
      exact .arrive hid ⟨q, hq⟩ he ha
    · have hw := RingRoleGeometry.of_trace hX hg (hs g hg) hst
      exact .arrive hid ⟨⟨128, by decide⟩,
        consumer_of_elected hpre hc hw lane (hLane he hc hd hst)⟩ he ha
  | inval _ _ ha => exact ((objects_single_lifetime hX _) r hr ha).elim
  | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
  | tensor _ _ _ ha | bulk _ _ _ _ ha | clc _ _ _ _ ha =>
    exact (no_completion hpre hX hs ht (.inr rfl) hr ha).elim
  | commit _ he hTarget _ => exact (no_commit hpre hX hs ht (.inr rfl) he rfl hTarget).elim

/-- The complete index ring follows from the tracked trace and the CTA's selected TMA lane. -/
theorem unit_ring_of_lane {mem0 : Mem0} {X : Execution} {cta : Nat} {slot : Fin 4} {lane : Fin 32}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hcta : cta < L.grid)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hLane : TmaConsumer P L X cta lane) :
    Unit.Ring L kernel Assumptions.all X (ready L cta slot) (free L cta slot)
      32 129 (producerThread L cta) (consumerThread L cta lane) :=
  unit_ring_of_records hpre hX hcta hs ht
    (ready_sources hpre hX hs ht) (free_sources hpre hX hs ht hLane)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
