-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TmaSource
public import Lemmas.Protocol.BarTable

@[expose] public section

/-! # The initialization of every mbarrier object

An object is initialized by CTA thread 0 of its CTA, once (`ThreadFacts.ring_event`: `init_site`
puts the initialization at the event the object's offset gives), so every initialization of an
object is one event (`init_event_eq`). Every other record of the object is issued by a role of the
object's cluster, to which the ring protocol's initialization is published (`ring_initialized`), and
the published initialization is the object's one initialization (`published_init`). So every other
record follows the initialization in the object's history, which is its first record, and it
succeeds (`init_first`, by `BarTable.first_record_of_site`): an object's records are published,
and its initialization is fault-free (`record_published`, `init_record_fault_free`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX AsyncCopy MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An initialization event's place: CTA thread 0 of the object's CTA, at the index of the object's
offset, with a valid count. -/
theorem init_site_of (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g j pc c : Nat}
    {m : Loc} (he : X.get (g, j) = some ⟨pc, .mbInit m c⟩) :
    g % L.block = 0 ∧ m.cta = g / L.block ∧ j = initIndexOf (m.addr - L.sharedBase) ∧ 0 < c ∧
      c ≤ 256 ∧ m.space = .shared ∧ L.sharedBase + 8 ≤ m.addr ∧
      (m.addr + 8 ≤ L.sharedBase + 144 ∨
        L.sharedBase + 160 ≤ m.addr ∧ m.addr + 8 ≤ L.sharedBase + 176) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  exact (ht.ring_event hg he hσ).init_site m c rfl

/-- **An object has one initialization event.** -/
theorem init_event_eq (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {E E' : EvId} {pc pc' c c' : Nat} {m : Loc}
    (hE : X.get E = some ⟨pc, .mbInit m c⟩) (hE' : X.get E' = some ⟨pc', .mbInit m c'⟩) :
    E = E' := by
  obtain ⟨g, j⟩ := E
  obtain ⟨g', j'⟩ := E'
  obtain ⟨h1, h2, h3, -⟩ := init_site_of hX ht hE
  obtain ⟨h1', h2', h3', -⟩ := init_site_of hX ht hE'
  have hgg : g = g' := by
    have e1 := Nat.div_add_mod g L.block
    have e2 := Nat.div_add_mod g' L.block
    have hq : g / L.block = g' / L.block := h2.symm.trans h2'
    rw [h1, hq] at e1
    rw [h1'] at e2
    exact e1.symm.trans e2
  rw [hgg, h3.trans h3'.symm]

/-- The initialization that a classified use of an object publishes to its issuer: the one of the
ring barrier. -/
theorem published_init (ht : ThreadFacts L X) {g j : Nat} {m : Loc}
    (hc : Classified L X g j m) :
    ∃ (E : EvId) (pc c : Nat), X.get E = some ⟨pc, .mbInit m c⟩ ∧ baseCausality L X E (g, j) := by
  obtain ⟨ρ, b, cta, hg, ⟨ev, he⟩, hσ, hb, hgrid, hcl, rfl, -⟩ := hc
  obtain ⟨pc, hinit, hpub⟩ := ht.ring_initialized (b := b) hg he hσ hb hgrid hcl
  exact ⟨_, _, _, hinit, hpub⟩

/-- **The initialization of an object is its first record, and succeeds**: it is the object's
one initialization event (`init_event_eq`), published to the issuer of every other record
(`published_init`). -/
theorem init_first (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {m : Loc} {E : EvId} {pc c : Nat}
    (hE : X.get E = some ⟨pc, .mbInit m c⟩) :
    ∃ r0, (X.objects m)[0]? = some r0 ∧ r0.id = .thread E ∧ r0.action = .init c ∧
      r0.fault = none := by
  obtain ⟨-, -, -, hc0, hc1, -⟩ := init_site_of hX ht hE
  have hsite : ∀ i pc' n, X.get i = some ⟨pc', .mbInit m n⟩ → i = E ∧ n = c := by
    intro i pc' n hi
    obtain rfl := init_event_eq hX ht hi hE
    rw [hE] at hi
    cases hi
    exact ⟨rfl, rfl⟩
  refine BarTable.first_record_of_site hX ⟨pc, hE⟩ ⟨hc0, by unfold limit; omega⟩ hsite
    fun s hs hn => ?_
  obtain ⟨E0, pc0, c0, hE0, hpub⟩ := published_init ht (noninit_source hpre hX ht hs hn)
  obtain rfl := init_event_eq hX ht hE hE0
  exact hpub

/-- **Every record of an object is published.** -/
theorem record_published (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) :
    ObjectPublished L X m r := by
  by_cases hn : ∃ n, r.action = .init n
  · exact Or.inl ⟨hn, fun _ hv => (no_inval hX ht hv).elim⟩
  · have hn' : ∀ n, r.action ≠ .init n := fun n h => hn ⟨n, h⟩
    obtain ⟨E, pc, c, hE, hpub⟩ := published_init ht (noninit_source hpre hX ht hr hn')
    obtain ⟨r0, hr0, hid0, ha0, hf0⟩ := init_first hpre hX ht hE
    refine Or.inr ⟨E, c, ⟨pc, hE⟩, ?_, .inl hpub, fun _ hv => (no_inval hX ht hv).elim⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hlt : 0 < j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · rw [hr0] at hj
        cases hj
        exact absurd ha0 (hn' c)
      · exact h
    exact ⟨0, j, r0, r, c, hr0, hid0, ha0, hf0, hj, rfl, hlt,
      (objects_noInval hX ht m).sameLifetime 0 j⟩

/-- **Every initialization record of an object is fault-free.** -/
theorem init_record_fault_free (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) {n : Nat}
    (ha : r.action = .init n) : r.fault = none := by
  cases record_source hX.tma.2.2.1 hr with
  | inval _ he _ => exact (no_inval hX ht ⟨_, he⟩).elim
  | init hid he ha' =>
    obtain ⟨r0, hr0, hid0, -, hf0⟩ := init_first hpre hX ht he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have : j = 0 := object_record_index_unique hX.tma.2.2.1 hj hr0 (hid.trans hid0.symm)
    subst this
    rw [hr0] at hj
    cases hj
    exact hf0
  | arrive hid he ha' => simp [ha] at ha'
  | wait hid he ha' => simp [ha] at ha'
  | tensor hid he hm ha' => simp [ha] at ha'
  | bulk hid he => exact (no_copy hX ht ⟨_, he⟩).elim
  | increment hid he => exact (no_asyncArrive hX ht ⟨_, he⟩).elim
  | arriveOn hid he => exact (no_asyncArrive hX ht ⟨_, he⟩).elim
  | commit hid he ht' ha' => simp [ha] at ha'
  | clc hid he hm htg ha' => simp [ha] at ha'

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
