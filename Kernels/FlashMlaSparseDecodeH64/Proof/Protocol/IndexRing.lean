-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingThreads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingHandoff
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingObjects
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSpins
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.IndexRingTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaIndexTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0IndexTrace

@[expose] public section

/-! # The index ring, from identified object and thread event sources -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing

open PTX PTX.Flow PTX.MbarRing
open IndexRingThreads

/-- The slot's publication object. -/
def ready (L : Launch) (cta : Nat) (slot : Fin 4) : Loc := (Mbar.validReady slot).loc L cta

/-- The slot's reuse object. -/
def free (L : Launch) (cta : Nat) (slot : Fin 4) : Loc := (Mbar.validFree slot).loc L cta

/-- An index event of the CTA on a block using the specified slot. -/
def AtIndex (P : Params) (L : Launch) (X : Execution) (cta : Nat) (slot : Fin 4)
    (g i : Nat) (site : Wg1Index.Site → Prop) : Prop :=
  ctaOf L g = cta ∧ ∃ d : Wg1Index.D, d.block % 4 = slot.val ∧ site d.site ∧
    Frame.stateAt (Machine.code P L) X g i = some (some (.index d))

/-- A TMA or softmax event of the CTA on a block using the specified slot. -/
def AtConsumer (P : Params) (L : Launch) (X : Execution) (cta : Nat) (slot : Fin 4)
    (g i : Nat) (wg0 : Wg0.Site) (tma : Wg1Tma.Site) : Prop :=
  ctaOf L g = cta ∧
    ((∃ d : Wg0.D, d.block % 4 = slot.val ∧ d.site = wg0 ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) ∨
     (∃ d : Wg1Tma.D, d.block % 4 = slot.val ∧ d.site = tma ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.tma d))))

/-- The remaining source and initialization facts for assembling a slot. The unit ring's
gates and poll parities are derived from the role traces. -/
structure Sources (P : Params) (L : Launch) (X : Execution) (cta : Nat) (slot : Fin 4)
    (tmaLane : Fin 32) : Prop where
  readyRecord : ∀ r ∈ X.objects (ready L cta slot),
    Unit.Source X (ready L cta slot) (fun g => ∃ p, g = producerThread L cta p) r
  freeRecord : ∀ r ∈ X.objects (free L cta slot),
    Unit.Source X (free L cta slot) (fun g => ∃ c, g = consumerThread L cta tmaLane c) r
  readyInit : PairTmaRing.InitFirst X (ready L cta slot) 32
  freeInit : PairTmaRing.InitFirst X (free L cta slot) 129
  publish : ∀ {g i : Nat} {e : Event} {sc : MbarScope},
    X.get (g, i) = some e → e.kind = .arrive (ready L cta slot) 0 1 true sc →
    AtIndex P L X cta slot g i (fun s => ∃ extra, s = .ready extra)
  reuse : ∀ {g i parity : Nat} {e : Event} {acq : Bool} {sc : MbarScope},
    X.get (g, i) = some e → e.kind = .wait (free L cta slot) parity true acq sc →
    AtIndex P L X cta slot g i (fun s => ∃ extra, s = .waitFree extra)
  awaitReady : ∀ {g i parity : Nat} {e : Event} {acq : Bool} {sc : MbarScope},
    X.get (g, i) = some e → e.kind = .wait (ready L cta slot) parity true acq sc →
    AtConsumer P L X cta slot g i .maskReady .waitCoord
  release : ∀ {g i : Nat} {e : Event} {sc : MbarScope},
    X.get (g, i) = some e → e.kind = .arrive (free L cta slot) 0 1 true sc →
    AtConsumer P L X cta slot g i .validFree .coordFree

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta : Nat} {slot : Fin 4}
    {tmaLane : Fin 32} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

private theorem publish_gate (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (H : Sources P L X cta slot tmaLane) {g i : Nat} {e : Event} {sc : MbarScope}
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (ready L cta slot) 0 1 true sc) :
    arrivals (ready L cta slot) ((X.tr g).take i) + 1 ≤
      okPolls (free L cta slot) ((X.tr g).take i) := by
  obtain ⟨hcta, d, hslot, ⟨extra, hd⟩, hst⟩ := H.publish he hk
  have hg := Frame.lt_of_get hX he
  have ht := (hs g hg).produces (hX.thr g hg)
  obtain ⟨ha, hp⟩ := IndexRingTrace.composed_ready_counts hpre ht hst hd
  change g / L.block = cta at hcta
  rw [hcta, hslot] at ha hp
  change arrivals (ready L cta slot) _ = _ at ha
  change okPolls (free L cta slot) _ = _ at hp
  rw [ha, hp]

private theorem release_gate (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (H : Sources P L X cta slot tmaLane) {g i : Nat} {e : Event} {sc : MbarScope}
    (he : X.get (g, i) = some e) (hk : e.kind = .arrive (free L cta slot) 0 1 true sc) :
    arrivals (free L cta slot) ((X.tr g).take i) + 1 ≤
      okPolls (ready L cta slot) ((X.tr g).take i) := by
  obtain ⟨hcta, hrole⟩ := H.release he hk
  have hg := Frame.lt_of_get hX he
  have ht := (hs g hg).produces (hX.thr g hg)
  rcases hrole with ⟨d, hslot, hd, hst⟩ | ⟨d, hslot, hd, hst⟩
  · obtain ⟨ha, hp⟩ := Wg0IndexTrace.composed_free_counts hpre ht hst hd
    rw [hcta, hslot] at ha hp
    change arrivals (free L cta slot) _ = _ at ha
    change okPolls (ready L cta slot) _ = _ at hp
    rw [ha, hp]
  · obtain ⟨ha, hp⟩ := TmaIndexTrace.composed_free_counts hpre ht hst hd
    rw [hcta, hslot] at ha hp
    change arrivals (free L cta slot) _ = _ at ha
    change okPolls (ready L cta slot) _ = _ at hp
    rw [ha, hp]

omit hpre hX in
private theorem ready_poll_fields {e : Event} {m m' : Loc} {parity use count : Nat}
    {ok acq : Bool} {scope : MbarScope}
    (hk : e.kind = .wait m parity true acq scope)
    (hwait : e.kind = .wait m' (use % 2) ok true .cta) (hcount : count = use) :
    acq = true ∧ parity % 2 = count % 2 := by
  obtain ⟨_, hp, _, ha, _⟩ := Kind.wait.inj (hk.symm.trans hwait)
  exact ⟨ha, by rw [hp, hcount]; simp⟩

private theorem ready_poll_facts (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (H : Sources P L X cta slot tmaLane) {g i parity : Nat} {e : Event} {acq : Bool}
    {sc : MbarScope} (he : X.get (g, i) = some e)
    (hk : e.kind = .wait (ready L cta slot) parity true acq sc) :
    acq = true ∧ parity % 2 = okPolls (ready L cta slot) ((X.tr g).take i) % 2 := by
  obtain ⟨hcta, hrole⟩ := H.awaitReady he hk
  have hg := Frame.lt_of_get hX he
  have ht := (hs g hg).produces (hX.thr g hg)
  rcases hrole with ⟨d, hslot, hd, hst⟩ | ⟨d, hslot, hd, hst⟩
  · have hcount := Wg0IndexTrace.composed_ready_counts hpre ht hst hd
    rw [hcta, hslot] at hcount
    change okPolls (ready L cta slot) _ = _ at hcount
    obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg) he hst
    obtain ⟨_, hk'⟩ := RingEvents.maskReady_wait hpre hd hf
    exact ready_poll_fields hk hk' hcount
  · have hcount := TmaIndexTrace.composed_ready_counts hpre ht hst hd
    rw [hcta, hslot] at hcount
    change okPolls (ready L cta slot) _ = _ at hcount
    obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg) he hst
    obtain ⟨_, hk'⟩ := RingEvents.validReady_wait hpre hd hf
    exact ready_poll_fields hk hk' hcount

private theorem free_poll_facts (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (H : Sources P L X cta slot tmaLane) {g i parity : Nat} {e : Event} {acq : Bool}
    {sc : MbarScope} (he : X.get (g, i) = some e)
    (hk : e.kind = .wait (free L cta slot) parity true acq sc) :
    acq = true ∧ parity % 2 = (okPolls (free L cta slot) ((X.tr g).take i) + 1) % 2 := by
  obtain ⟨hcta, d, hslot, ⟨extra, hd⟩, hst⟩ := H.reuse he hk
  have hg := Frame.lt_of_get hX he
  have ht := (hs g hg).produces (hX.thr g hg)
  have hcount := (IndexRingTrace.composed_free_counts hpre ht hst hd).2
  change g / L.block = cta at hcta
  rw [hcta, hslot] at hcount
  change 1 - d.block / 4 % 2 = (okPolls (free L cta slot) _ + 1) % 2 at hcount
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg) he hst
  obtain ⟨_, hk'⟩ := RingEvents.validFree_wait hpre hd hf
  obtain ⟨_, hp, _, ha, _⟩ := Kind.wait.inj (hk.symm.trans hk')
  exact ⟨ha, by omega⟩

/-- Assemble a concrete 32-by-129 index ring from the classified sources of its two objects.
The thread traces supply both gates and both parity sequences. -/
theorem unit_ring (hcta : cta < L.grid) (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (H : Sources P L X cta slot tmaLane) :
    Unit.Ring L kernel Assumptions.all X (ready L cta slot) (free L cta slot)
      32 129 (producerThread L cta) (consumerThread L cta tmaLane) where
  F :=
    { pos := by decide
      inj := producerThread_injective L cta
      src := H.readyRecord
      init := H.readyInit
      noInval := objects_single_lifetime hX _
      parity := fun he => by
        rw [Nat.add_zero]
        exact (ready_poll_facts hpre hX hs H he rfl).2
      δ_le := by decide }
  E :=
    { pos := by decide
      inj := consumerThread_injective L cta tmaLane
      src := H.freeRecord
      init := H.freeInit
      noInval := objects_single_lifetime hX _
      parity := fun he => (free_poll_facts hpre hX hs H he rfl).2
      δ_le := by decide }
  gateP he := publish_gate hpre hX hs H he rfl
  gateC he := release_gate hpre hX hs H he rfl
  spins _ _ _ _ _ _ he := RingSpins.successful_poll hX he
  acqF he := (ready_poll_facts hpre hX hs H he rfl).1
  acqE he := (free_poll_facts hpre hX hs H he rfl).1
  cta := sameCta hpre hcta tmaLane

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
