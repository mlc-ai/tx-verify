-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReadyPhases
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadyCoverage
import Mathlib.Data.Fintype.Prod

@[expose] public section

/-! # A second WG0 release depends on a later producer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Any pool of enough distinct ready records includes a producer above the use bound. -/
theorem later_producer_of_ready_pool {g i n block : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    {positions : Finset Nat} (hCard : positions.card = (n + 1 + 1) * 32)
    (hRecords : ∀ t ∈ positions,
      ∃ (r : Record Ref) (h j : Nat) (f : Event) (z : Wg1Index.D) (extra : Bool),
        (X.objects (ready L (ctaOf L g) (indexSlot block)))[t]? = some r ∧
        r.id = .thread (h, j) ∧ ctaOf L h = ctaOf L g ∧ z.block % 4 = block % 4 ∧
        z.site = .ready extra ∧ X.get (h, j) = some f ∧
        Frame.stateAt (Machine.code P L) X h j = some (some (.index z)) ∧
        baseCausality L X (h, j) (g, i)) :
    ∃ (h j : Nat) (f : Event) (z : Wg1Index.D) (extra : Bool),
      X.get (h, j) = some f ∧ Frame.stateAt (Machine.code P L) X h j = some (some (.index z)) ∧
      ctaOf L h = ctaOf L g ∧ z.block % 4 = block % 4 ∧ z.site = .ready extra ∧
      n < z.block / 4 ∧ baseCausality L X (h, j) (g, i) := by
  classical
  by_contra hNone
  let cta := ctaOf L g
  let log := X.objects (ready L cta (indexSlot block))
  have from_pos (t : Nat) (ht : t ∈ positions) :
      ∃ (key : Fin 32 × Fin (n + 1)) (r : Record Ref) (j : Nat) (f : Event)
        (z : Wg1Index.D) (extra : Bool),
        log[t]? = some r ∧ r.id = .thread (producerThread L cta key.1, j) ∧
        z.block / 4 = key.2.val ∧ z.block % 4 = block % 4 ∧ z.site = .ready extra ∧
        X.get (producerThread L cta key.1, j) = some f ∧
        Frame.stateAt (Machine.code P L) X (producerThread L cta key.1) j =
          some (some (.index z)) := by
    obtain ⟨r, h, j, f, z, extra, hr, hid, hc, hSlot, hz, hf, hState, hOrder⟩ := hRecords t ht
    have hBound : z.block / 4 ≤ n := by
      by_contra! hp
      exact hNone ⟨h, j, f, z, extra, hf, hState, hc, hSlot, hz, by omega, hOrder⟩
    have hh := Frame.lt_of_get hX hf
    have hw := RingRoleGeometry.of_trace hX hh (hs h hh).machine hState
    obtain ⟨lane, hLane⟩ := producer_of_warp hpre hc hw
    rw [hLane] at hid hf hState
    exact ⟨(lane, ⟨z.block / 4, by omega⟩), r, j, f, z, extra, hr, hid, rfl, hSlot, hz, hf, hState⟩
  let f (t : Nat) : Fin 32 × Fin (n + 1) :=
    if ht : t ∈ positions then (from_pos t ht).choose else (0, 0)
  have chosen (t : Nat) (ht : t ∈ positions) :
      ∃ (r : Record Ref) (j : Nat) (e : Event) (z : Wg1Index.D) (extra : Bool),
        log[t]? = some r ∧ r.id = .thread (producerThread L cta (f t).1, j) ∧
        z.block / 4 = (f t).2.val ∧ z.block % 4 = block % 4 ∧
        z.site = .ready extra ∧
        X.get (producerThread L cta (f t).1, j) = some e ∧
        Frame.stateAt (Machine.code P L) X (producerThread L cta (f t).1) j =
          some (some (.index z)) := by
    have hf : f t = (from_pos t ht).choose := by simp only [f, dite_eq_left ht]
    rw [hf]
    exact (from_pos t ht).choose_spec
  have hInj : Set.InjOn f positions := by
    intro t ht u hu hEq
    obtain ⟨r, j, e, z, extra, hr, hid, hu0, hb, hz, he, hs0⟩ := chosen t ht
    obtain ⟨r', j', e', z', extra', hr', hid', hu1, hb', hz', he', hs1⟩ := chosen u hu
    rw [← hEq] at hid' he' hs1 hu1
    have hg := Frame.lt_of_get hX he
    have hj := ready_same_block_unique hpre hX (hs _ hg).machine he he' hs0 hs1 hz hz'
      (by omega : z.block = z'.block)
    rw [hj] at hid
    exact hX.object_index_eq hr hr' (hid.trans hid'.symm)
  have hLimit := Finset.card_le_card (Finset.subset_univ (positions.image f))
  rw [Finset.card_image_of_injOn hInj, hCard, Finset.card_univ] at hLimit
  simp only [Fintype.card_prod, Fintype.card_fin] at hLimit
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
