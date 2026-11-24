-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadyCount
import Lemmas.Protocol.CountNth

@[expose] public section

/-! # Recovering the selected producer from actual ready-phase records -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An index lane releases a given block on its ready slot at most once. -/
theorem ready_same_block_unique {g i j : Nat} {d d' : Wg1Index.D}
    {ea eb : Event} {extra extra' : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some ea) (hf : X.get (g, j) = some eb)
    (ha : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hb : Frame.stateAt (Machine.code P L) X g j = some (some (.index d')))
    (haSite : d.site = .ready extra) (hbSite : d'.site = .ready extra')
    (hBlock : d.block = d'.block) : i = j := by
  let m := ready L (ctaOf L g) (indexSlot d.block)
  have trace := hs.produces (hX.thr g (Frame.lt_of_get hX he))
  have hACount := (IndexRingTrace.composed_ready_counts hpre trace ha haSite).1
  have hBCount := (IndexRingTrace.composed_ready_counts hpre trace hb hbSite).1
  change arrivals m ((X.tr g).take i) = d.block / 4 at hACount
  rw [← hBlock] at hBCount
  change arrivals m ((X.tr g).take j) = d.block / 4 at hBCount
  obtain ⟨_, hfa⟩ := RingEvents.fired_of_trace hX hs he ha
  obtain ⟨_, hfb⟩ := RingEvents.fired_of_trace hX hs hf hb
  have hka := RingEvents.validReady_arrive hpre haSite hfa
  have hkb := RingEvents.validReady_arrive hpre hbSite hfb
  change ea.kind = .arrive m 0 1 true .cta at hka
  rw [← hBlock] at hkb
  change eb.kind = .arrive m 0 1 true .cta at hkb
  have before {a b : Nat} {e : Event} (h : a < b) (he : X.get (g, a) = some e)
      (hk : e.kind = .arrive m 0 1 true .cta) :
      arrivals m ((X.tr g).take a) < arrivals m ((X.tr g).take b) := by
    have hArr : arrivesOn m e = true := by simp [arrivesOn, sourceArrive, hk]
    have hOne := countP_take_succ he hArr
    have hLe := countP_take_mono (arrivesOn m) (X.tr g) (show a + 1 ≤ b by omega)
    unfold arrivals
    omega
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · have := before hlt he hka
    omega
  · exact heq
  · have := before hgt hf hkb
    omega

/-- Once the actual ready records are aligned to the current block, all 32 producer lanes are
represented. The same producer cannot contribute twice for one block. -/
theorem ready_positions_cover_lanes {cta block : Nat} {positions : Finset Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hCard : positions.card = 32)
    (he : ∀ t ∈ positions, ∃ (r : Record Ref) (g i : Nat) (d : Wg1Index.D) (extra : Bool),
      (X.objects (ready L cta (indexSlot block)))[t]? = some r ∧ r.id = .thread (g, i) ∧
      ctaOf L g = cta ∧ d.block = block ∧ d.site = .ready extra ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.index d))) :
    ∀ lane : Fin 32, ∃ t ∈ positions, ∃ (r : Record Ref) (i : Nat) (d : Wg1Index.D) (extra : Bool),
      (X.objects (ready L cta (indexSlot block)))[t]? = some r ∧
      r.id = .thread (producerThread L cta lane, i) ∧ d.block = block ∧ d.site = .ready extra ∧
      Frame.stateAt (Machine.code P L) X (producerThread L cta lane) i =
        some (some (.index d)) := by
  classical
  let m := ready L cta (indexSlot block)
  have from_pos (t : Nat) (ht : t ∈ positions) :
      ∃ (lane : Fin 32) (r : Record Ref) (i : Nat) (d : Wg1Index.D) (extra : Bool),
        (X.objects m)[t]? = some r ∧ r.id = .thread (producerThread L cta lane, i) ∧
        d.block = block ∧ d.site = .ready extra ∧
        Frame.stateAt (Machine.code P L) X (producerThread L cta lane) i =
          some (some (.index d)) := by
    obtain ⟨r, g, i, d, extra, hget, hid, hCta, hBlock, hSite, hState⟩ := he t ht
    obtain ⟨e, hEvent⟩ := hX.object_thread_record_present (List.mem_of_getElem? hget) hid
    have hg := Frame.lt_of_get hX hEvent
    have hw := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
    obtain ⟨lane, hLane⟩ := producer_of_warp hpre hCta hw
    cases hLane
    exact ⟨lane, r, i, d, extra, hget, hid, hBlock, hSite, hState⟩
  let f (t : Nat) : Fin 32 := if ht : t ∈ positions then (from_pos t ht).choose else 0
  have hChoice (t : Nat) (ht : t ∈ positions) :
      ∃ (r : Record Ref) (i : Nat) (d : Wg1Index.D) (extra : Bool),
        (X.objects m)[t]? = some r ∧ r.id = .thread (producerThread L cta (f t), i) ∧
        d.block = block ∧ d.site = .ready extra ∧
        Frame.stateAt (Machine.code P L) X (producerThread L cta (f t)) i =
          some (some (.index d)) := by
    have hf : f t = (from_pos t ht).choose := by simp only [f, dite_eq_left ht]
    rw [hf]
    exact (from_pos t ht).choose_spec
  have hInj : Set.InjOn f positions := by
    intro t ht u hu hEq
    obtain ⟨r, i, d, extra, hr, hrid, hd, hds, hst⟩ := hChoice t ht
    obtain ⟨r', j, d', extra', hr', hrid', hd', hds', hst'⟩ := hChoice u hu
    rw [← hEq] at hrid' hst'
    obtain ⟨e, he⟩ := hX.object_thread_record_present (List.mem_of_getElem? hr) hrid
    obtain ⟨e', he'⟩ := hX.object_thread_record_present (List.mem_of_getElem? hr') hrid'
    have hg := Frame.lt_of_get hX he
    have hij := ready_same_block_unique hpre hX (hs _ hg).machine he he' hst hst' hds hds'
      (hd.trans hd'.symm)
    rw [hij] at hrid
    exact hX.object_index_eq hr hr' (hrid.trans hrid'.symm)
  have hImage : positions.image f = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injOn hInj, hCard]
    simp
  intro lane
  obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp (show lane ∈ positions.image f by rw [hImage]; simp)
  exact ⟨t, ht, hEq ▸ hChoice t ht⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
