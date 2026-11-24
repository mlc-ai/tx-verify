-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingInit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingPolls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.InitCtaPublication

@[expose] public section

/-! # Checked initialization of the index ring in the actual CTA trace -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing

open PTX MBarrier AsyncCopy PTX.MbarRing
open IndexRingThreads

private theorem index_state {P : Params} {L : Launch} {X : Execution} {g i cta : Nat}
    {slot : Fin 4} {S : Wg1Index.Site → Prop}
    (h : AtIndex P L X cta slot g i S) :
    ctaOf L g = cta ∧ ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
      ∀ s, d ≠ .prologue s := by
  obtain ⟨hc, d, _, _, hd⟩ := h
  exact ⟨hc, .index d, hd, by intro s he; cases he⟩

private theorem consumer_state {P : Params} {L : Launch} {X : Execution} {g i cta : Nat}
    {slot : Fin 4} {S : Wg0.Site} {T : Wg1Tma.Site}
    (h : AtConsumer P L X cta slot g i S T) :
    ctaOf L g = cta ∧ ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
      ∀ s, d ≠ .prologue s := by
  obtain ⟨hc, h⟩ := h
  rcases h with ⟨d, _, _, hd⟩ | ⟨d, _, _, hd⟩
  · exact ⟨hc, .wg0 d, hd, by intro s he; cases he⟩
  · exact ⟨hc, .tma d, hd, by intro s he; cases he⟩

variable {P : Params} {L : Launch} {mem0 : Mem0}

private theorem unit_user_role {X : Execution} {cta : Nat} {slot : Fin 4} {m : Loc} {r : Record Ref}
    {prod : Nat → Prop} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hm : m = ready L cta slot ∨ m = free L cta slot) (hsource : Unit.Source X m prod r)
    (hn : ∀ n, r.action ≠ .init n) :
    ∃ g i e d, r.id.issuer = (g, i) ∧ X.get (g, i) = some e ∧ ctaOf L g = cta ∧
      Frame.stateAt (Machine.code P L) X g i = some (some d) ∧ ∀ s, d ≠ .prologue s := by
  cases hsource with
  | init ha => exact (hn _ ha).elim
  | @poll g i _ _ _ _ _ hid he _ =>
    have hg := Frame.lt_of_get hX he
    have role : ctaOf L g = cta ∧
        ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
          ∀ s, d ≠ .prologue s := by
      rcases hm with rfl | rfl
      · exact consumer_state (await_ready_source hpre hX (hs _ hg) ht he rfl).1
      · exact index_state (reuse_source hpre hX (hs _ hg) ht he rfl).1
    obtain ⟨hc, d, hst, hr⟩ := role
    exact ⟨_, _, _, d, by rw [hid]; rfl, he, hc, hst, hr⟩
  | @arrive g i _ _ hid _ he _ =>
    have hg := Frame.lt_of_get hX he
    have role : ctaOf L g = cta ∧
        ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some d) ∧
          ∀ s, d ≠ .prologue s := by
      rcases hm with rfl | rfl
      · exact index_state (publish_source hpre hX (hs _ hg) ht he rfl).1
      · exact consumer_state (release_source hpre hX (hs _ hg) ht he rfl).1
    obtain ⟨hc, d, hst, hr⟩ := role
    exact ⟨_, _, _, d, by rw [hid]; rfl, he, hc, hst, hr⟩

private theorem slot_init_first {X : Execution} {cta : Nat} {slot : Fin 4} {j : Fin 23} {m : Loc}
    {prod : Nat → Prop} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hm : m = ready L cta slot ∨ m = free L cta slot) (hl : initTable.loc L cta j = m)
    (hRecord : ∀ r ∈ X.objects m, Unit.Source X m prod r) :
    PairTmaRing.InitFirst X m (initCount j) := by
  obtain ⟨init, hinit⟩ := exists_init_sites hpre hX hs ht
  subst m
  apply published_init_first hX hinit cta j
  intro r hr hn
  obtain ⟨g, i, e, d, hid, he, hc, hst, hrole⟩ :=
    unit_user_role hpre hX hs ht hm (hRecord r hr) hn
  obtain ⟨a, hMb, hBefore⟩ := InitCtaPublication.completed_init_before_role hpre hX hs ht
    he hst hrole j
  rw [hc] at hMb
  change X.MbInit a (initTable.loc L cta j) (initCount j) at hMb
  have ha := (hinit j cta a _ _ trivial hMb.choose_spec).1
  rw [← ha, hid]
  exact ⟨hMb, .inl hBefore⟩

/-- Classifying the records of each slot as unit operations suffices to construct the ring.
The prologue gate supplies both checked initializations. -/
theorem unit_ring_of_records {X : Execution} {cta : Nat} {slot : Fin 4} {tmaLane : Fin 32}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hcta : cta < L.grid)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : ∀ r ∈ X.objects (ready L cta slot),
      Unit.Source X (ready L cta slot) (fun g => ∃ p, g = producerThread L cta p) r)
    (hf : ∀ r ∈ X.objects (free L cta slot),
      Unit.Source X (free L cta slot) (fun g => ∃ c, g = consumerThread L cta tmaLane c) r) :
    Unit.Ring L kernel Assumptions.all X (ready L cta slot) (free L cta slot)
      32 129 (producerThread L cta) (consumerThread L cta tmaLane) :=
  unit_ring hpre hX hcta hs {
    readyRecord := hr
    freeRecord := hf
    readyInit := by
      rw [← ready_entry_count slot]
      exact slot_init_first hpre hX hs ht (.inl rfl) (ready_entry_loc L cta slot) hr
    freeInit := by
      rw [← free_entry_count slot]
      exact slot_init_first hpre hX hs ht (.inr rfl) (free_entry_loc L cta slot) hf
    publish := fun he hk => (publish_source hpre hX (hs _ (Frame.lt_of_get hX he)) ht he hk).1
    reuse := fun he hk => (reuse_source hpre hX (hs _ (Frame.lt_of_get hX he)) ht he hk).1
    awaitReady := fun he hk =>
      (await_ready_source hpre hX (hs _ (Frame.lt_of_get hX he)) ht he hk).1
    release := fun he hk => (release_source hpre hX (hs _ (Frame.lt_of_get hX he)) ht he hk).1
  }

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
