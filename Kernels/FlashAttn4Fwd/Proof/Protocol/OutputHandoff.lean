-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputStaging
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsCreditGate
public import Lemmas.Protocol.UnitRingGate

@[expose] public section

/-! # The output barriers form a ring of two unit objects

Stage `st`'s staged barrier (`stagedBar`, count 128) and free barrier (`freeBar`, count 32) of a
CTA `c < grid` are a ring of two unit objects (`MbarRing.Unit.Ring`, `unitRing`): the CTA's 128
correction threads (`Stats.corrThread`) make the staged barrier's release arrivals, each after
more successful polls of the free barrier than its earlier staged arrivals, and the CTA's 32 store
lanes (`storeThread`) make the free barrier's, each after more successful polls of the staged
barrier than its earlier free arrivals (`OutputFacts.staged_arrive`, `free_arrive`). The store
lanes poll the staged barrier at the parity of their earlier successful polls, the correction
threads the free barrier at that parity plus one (`staged_poll`, `free_poll`); no copy, commit,
bulk copy, cancellation request or invalidation touches either barrier. Each history starts with
its only initialization (`OutputInit`, a premise as `RingInit`).

The ring's attribution (`MbarRing.Items.Ring`) gives the handoffs of both barriers:
`OutputHandoff` (`outputHandoff`). Both barriers are gated unit objects
(`MbarRing.Unit.Ring.fullGate`, `emptyGate`), so a store lane blocked at a staged wait and a
correction thread blocked at a free wait are one use ahead of a phase some producer has not
completed (`StoreBlocked`, `storeBlocked`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof
open AsyncCopy

noncomputable section

namespace Output

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- Store lane `b` of CTA `c` (warp 13). -/
def storeThread (L : Launch) (c : Nat) (b : Fin 32) : Nat := c * L.block + (416 + b.val)

/-- **The initialization premise** of the output barriers: each history starts with its only
initialization, without fault, with the barrier's count. -/
def OutputInit (L : Launch) (X : Execution) : Prop :=
  ∀ c st, st < 2 → PairTmaRing.InitFirst X (stagedBar L c st) 128 ∧
    PairTmaRing.InitFirst X (freeBar L c st) 32

theorem storeThread_facts (hpre : Pre P L mem0) {c : Nat} (hc : c < L.grid) (b : Fin 32) :
    storeThread L c b < L.threads ∧ ctaOf L (storeThread L c b) = c := by
  have hb := hpre.block
  have := b.isLt
  unfold storeThread ctaOf Launch.threads
  rw [hb] at *
  exact ⟨by nlinarith, by omega⟩

/-- A store lane of CTA `c` is one of its 32. -/
theorem storeThread_of (hpre : Pre P L mem0) {c g : Nat} (h : storeIn L c g) :
    ∃ b, g = storeThread L c b := by
  obtain ⟨-, hc, h13⟩ := h
  have hb := hpre.block
  simp only [ctaOf, warpOf, hb] at hc h13
  refine ⟨⟨g % 512 - 416, by omega⟩, ?_⟩
  unfold storeThread
  rw [hb]
  simp only
  omega

/-- **The output barriers of stage `st` of CTA `c` are a ring of two unit objects.** -/
theorem unitRing (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : OutputFacts L X)
    (htm : TmemFacts L X) (hinit : OutputInit L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {c st : Nat} (hc : c < L.grid) (hst : st < 2) :
    MbarRing.Unit.Ring L K A X (stagedBar L c st) (freeBar L c st) 128 32 (Stats.corrThread L c)
      (storeThread L c) where
  F :=
    { pos := by decide
      inj := Stats.corrThread_inj L c
      src := fun r hr => by
        cases record_source hX.tma.2.2.1 hr with
        | init _ _ ha => exact .init ha
        | inval _ he _ => exact (htm.no_inval he).elim
        | @arrive g j pc tx cnt rel sc hid he ha =>
          have hg := event_thread_lt hX he
          obtain ⟨h8, h12, hcg, rfl, rfl, rfl, -⟩ := ht.staged_arrive hg hst he
          subst hcg
          exact .arrive hid (Stats.corrThread_of hpre ⟨hg, rfl, h8, h12⟩) he ha
        | wait hid he ha => exact .poll hid he ha
        | tensor _ he hm _ => exact ((ht.stage_tensor hst he).1 hm).elim
        | increment _ he _ => exact (htm.no_arriveOn he).elim
        | arriveOn _ he _ _ _ => exact (htm.no_arriveOn he).elim
        | bulk _ he _ _ _ => exact (htm.no_bulk he).elim
        | commit _ he htg _ => exact ((ht.stage_commit hst he).1 htg).elim
        | clc _ he _ _ _ => exact (htm.no_clc he).elim
      init := (hinit c st hst).1
      noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => htm.no_inval he) _
      parity := fun he => by
        rw [Nat.add_zero]
        exact (ht.staged_poll (event_thread_lt hX he) hst he).2.2.1
      δ_le := Nat.zero_le 1 }
  E :=
    { pos := by decide
      inj := fun a b h => Fin.ext (by unfold storeThread at h; omega)
      src := fun r hr => by
        cases record_source hX.tma.2.2.1 hr with
        | init _ _ ha => exact .init ha
        | inval _ he _ => exact (htm.no_inval he).elim
        | @arrive g j pc tx cnt rel sc hid he ha =>
          have hg := event_thread_lt hX he
          obtain ⟨h13, hcg, rfl, rfl, rfl, -⟩ := ht.free_arrive hg hst he
          subst hcg
          exact .arrive hid (storeThread_of hpre ⟨hg, rfl, h13⟩) he ha
        | wait hid he ha => exact .poll hid he ha
        | tensor _ he hm _ => exact ((ht.stage_tensor hst he).2 hm).elim
        | increment _ he _ => exact (htm.no_arriveOn he).elim
        | arriveOn _ he _ _ _ => exact (htm.no_arriveOn he).elim
        | bulk _ he _ _ _ => exact (htm.no_bulk he).elim
        | commit _ he htg _ => exact ((ht.stage_commit hst he).2 htg).elim
        | clc _ he _ _ _ => exact (htm.no_clc he).elim
      init := (hinit c st hst).2
      noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => htm.no_inval he) _
      parity := fun he => (ht.free_poll (event_thread_lt hX he) hst he).2.2.2.1
      δ_le := le_refl 1 }
  gateP he := (ht.staged_arrive (event_thread_lt hX he) hst he).2.2.2.2.2.2
  gateC he := (ht.free_arrive (event_thread_lt hX he) hst he).2.2.2.2.2
  spins := hspin
  acqF he := (ht.staged_poll (event_thread_lt hX he) hst he).2.2.2 rfl
  acqE he := (ht.free_poll (event_thread_lt hX he) hst he).2.2.2.2 rfl
  cta a b := by
    obtain ⟨h1, h2, -⟩ := Stats.corrThread_facts hpre hc a
    obtain ⟨h3, h4⟩ := storeThread_facts hpre hc b
    exact ⟨h1, h3, by unfold ctaOf at h2 h4; rw [h2, h4]⟩

/-- A handoff with consumers of a CTA beyond the grid holds: there are none. -/
theorem handoff_out {c : Nat} (hc : ¬ c < L.grid) {m : Loc} {prod cons : Nat → Prop} {δ : Nat}
    (hcons : ∀ h, cons h → h < L.threads ∧ ctaOf L h = c) :
    MbarRing.UnitHandoff L X m prod cons δ := by
  intro h _ _ _ _ _ _ hh
  obtain ⟨hlt, hcta⟩ := hcons h hh
  exact absurd (hcta ▸ cta_lt hlt) hc

/-- **The output handoffs** (`OutputHandoff`). -/
theorem outputHandoff (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : OutputFacts L X)
    (htm : TmemFacts L X) (hinit : OutputInit L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit) :
    OutputHandoff L X := by
  intro c st hst
  by_cases hc : c < L.grid
  · have R := unitRing hpre hX ht htm hinit hspin hc hst
    exact ⟨MbarRing.UnitHandoff.mono (R.full_handoff hX)
        (fun _ hg => Stats.corrThread_of hpre hg) (fun _ hh => storeThread_of hpre hh),
      MbarRing.UnitHandoff.mono (R.empty_handoff hX)
        (fun _ hg => storeThread_of hpre hg) (fun _ hh => Stats.corrThread_of hpre hh)⟩
  · exact ⟨handoff_out hc fun _ hh => ⟨hh.1, hh.2.1⟩, handoff_out hc fun _ hh => ⟨hh.1, hh.2.1⟩⟩

/-- **Who blocks the output stages.** A store lane of CTA `c` whose stage's staged barrier ends in
a phase of the parity its next poll does not find has polled successfully as many times as that
phase, and some correction thread of the CTA has exactly that phase's number of counted staged
arrivals; a correction thread whose stage's free barrier ends in such a phase has polled
successfully once more than it, and some store lane has exactly that phase's number of counted
free arrivals. -/
def StoreBlocked (L : Launch) (X : Execution) : Prop :=
  ∀ c st, st < 2 →
    (∀ h, storeIn L c h → ∀ {before : MBarrier.State},
      MBarrier.stateBefore (X.objects (stagedBar L c st)) (X.objects (stagedBar L c st)).length =
        some before →
      before.phase % 2 = okPolls (stagedBar L c st) (X.tr h) % 2 →
        before.phase = okPolls (stagedBar L c st) (X.tr h) ∧
          ∃ a, (X.objects (stagedBar L c st)).countP
            (MbarRing.Unit.unitsOf (Stats.corrThread L c a)) = before.phase) ∧
    (∀ h, Stats.corrIn L c h → ∀ {before : MBarrier.State},
      MBarrier.stateBefore (X.objects (freeBar L c st)) (X.objects (freeBar L c st)).length =
        some before →
      before.phase % 2 = (okPolls (freeBar L c st) (X.tr h) + 1) % 2 →
        before.phase + 1 = okPolls (freeBar L c st) (X.tr h) ∧
          ∃ b, (X.objects (freeBar L c st)).countP
            (MbarRing.Unit.unitsOf (storeThread L c b)) = before.phase)

theorem storeBlocked (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : OutputFacts L X)
    (htm : TmemFacts L X) (hinit : OutputInit L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit) :
    StoreBlocked L X := by
  intro c st hst
  refine ⟨fun h hh before hs hp => ?_, fun h hh before hs hp => ?_⟩
  · have R := unitRing hpre hX ht htm hinit hspin (hh.2.1 ▸ cta_lt hh.1) hst
    have := (R.fullGate hX).blocked hX (storeThread_of hpre hh) hs (by rw [Nat.add_zero]; exact hp)
    rwa [Nat.add_zero] at this
  · have R := unitRing hpre hX ht htm hinit hspin (hh.2.1 ▸ cta_lt hh.1) hst
    exact (R.emptyGate hX).blocked hX (Stats.corrThread_of hpre hh) hs hp

end Output

end
end PTX.Kernels.FlashAttn4Fwd.Proof
