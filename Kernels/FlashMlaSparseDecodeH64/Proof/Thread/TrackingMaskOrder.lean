-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaReadyDescent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadyCoverage
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReadyPhases
import Lemmas.Order.OrderBaseCausality
import Mathlib.Data.Fintype.Prod

@[expose] public section

/-! # A mask read precedes later producers of the slot it holds -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Protocol Protocol.IndexRing
open IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem gather_return_bound {g i block : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) :
    ∃ leader, GatherReturnBound P L X (g, i) block leader := by
  let cta := ctaOf L g
  let slot := indexSlot block
  let m := free L cta slot
  obtain ⟨lane, hLane⟩ := Wg1TmaLeader.cta_issuer (cta := cta) hpre hX
    (fun h hh => (hs h hh).machine)
  refine ⟨cta * L.block + 160 + lane.val, ?_⟩
  intro a t tag hGet hWarp _
  have ha := Frame.lt_of_get hX hGet
  obtain ⟨⟨hCta, hRole⟩, _⟩ := release_source_at_tracked_event hpre hX (hs a ha).machine
    (tracked_tma_warp hpre hX hs hWarp t) hGet
    (rfl : (Event.kind ⟨tag, .arrive m 0 1 true .cta⟩) = .arrive m 0 1 true .cta)
  rcases hRole with ⟨z, _, _, hState⟩ | ⟨z, hSlot, hSite, hState⟩
  · have hGroup := RingRoleGeometry.of_trace hX ha (hs a ha).machine hState
    change wgOf L a = 0 at hGroup
    unfold wgOf warpOf at *
    omega
  · refine ⟨hLane a t z hCta hState (by simp [hSite]), ?_⟩
    have hTrace := (hs a ha).machine.produces (hX.thr a ha)
    have hCount := (TmaIndexTrace.composed_free_counts hpre hTrace hState hSite).1
    change z.block % 4 = slot.val at hSlot
    change arrivals (free L (ctaOf L a) (indexSlot z.block)) ((X.tr a).take t) =
      z.block / 4 at hCount
    rw [hCta, show indexSlot z.block = slot from Fin.ext hSlot] at hCount
    change arrivals m ((X.tr a).take t) = z.block / 4 at hCount
    by_cases hUse : z.block / 4 ≤ block / 4
    · exact .inl (hCount.le.trans hUse)
    · obtain ⟨h, j, e, d, extra, he, hd, hc, hs', hz, hUse', hBefore⟩ :=
        tma_depends_on_later_producer hpre hX hs hGet hState hSite (Nat.lt_of_not_ge hUse)
      exact .inr ⟨h, j, e, d, extra, he, hd, hc.trans hCta, hs'.trans hSlot, hz, hUse', hBefore⟩

theorem mask_before_future_producer {g i h j : Nat} {d : Wg0.D} {z : Wg1Index.D}
    {e f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hMask : d.site = .maskRead)
    (hf : X.get (h, j) = some f)
    (hz : Frame.stateAt (Machine.code P L) X h j = some (some (.index z)))
    (hProd : IndexProductionSite z.site) (hCta : ctaOf L h = ctaOf L g)
    (hSlot : z.block % 4 = d.block % 4) (hLater : d.block / 4 < z.block / 4) :
    baseCausality L X (g, i) (h, j) := by
  have hg := Frame.lt_of_get hX he
  have hWg := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  have hCount := (Wg0IndexTrace.composed_mask_read_counts hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hd hMask).1
  obtain ⟨_, hGather⟩ := gather_return_bound (g := g) (i := i) (block := d.block) hpre hX hs
  exact consumer_before_future_producer hpre hX hs hGather (.inl hWg) hCount hf hz hProd hCta
    hSlot hLater

/-- The source records before the mask read cover every producer of the current slot use. -/
theorem mask_publication {g i : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hMask : d.site = .maskRead)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) (lane : Fin 32) :
    let p := producerThread L (ctaOf L g) lane
    ∃ (j : Nat) (f : Event) (z : Wg1Index.D) (extra : Bool),
      X.get (p, j) = some f ∧ Frame.stateAt (Machine.code P L) X p j = some (some (.index z)) ∧
      z.site = .ready extra ∧ z.block = d.block ∧ baseCausality L X (p, j) (g, i) := by
  classical
  let cta := ctaOf L g
  let n := d.block / 4
  let log := X.objects (ready L cta (indexSlot d.block))
  obtain ⟨records, hCard, hOrigin⟩ := softmax_ready_pool (n := n) hpre hX hs he hd
    (.inr hMask) le_rfl hPrior
  let Key := Fin 32 × Fin (n + 1)
  let Fits (p : records) (key : Key) : Prop :=
    let h := producerThread L cta key.1
    ∃ (r : Record Ref) (j : Nat) (f : Event) (z : Wg1Index.D) (extra : Bool),
      log[p.val]? = some r ∧ r.id = .thread (h, j) ∧ X.get (h, j) = some f ∧
      Frame.stateAt (Machine.code P L) X h j = some (some (.index z)) ∧ z.site = .ready extra ∧
      z.block % 4 = d.block % 4 ∧ z.block / 4 = key.2.val ∧ baseCausality L X (h, j) (g, i)
  have assign (p : records) : ∃ key, Fits p key := by
    obtain ⟨r, h, j, f, z, extra, hr, hid, hc, hSlot, hSite, hf, hz, hOrder⟩ :=
      hOrigin p.val p.property
    have hBound : z.block / 4 ≤ n := by
      by_contra! hLater
      have hFuture := mask_before_future_producer hpre hX hs he hd hMask hf hz
        (.inl ⟨extra, hSite⟩) hc hSlot hLater
      exact baseCausality_irrefl hX.object.cause (hOrder.trans hFuture)
    have hWarp := RingRoleGeometry.of_trace hX (Frame.lt_of_get hX hf)
      (hs h (Frame.lt_of_get hX hf)).machine hz
    obtain ⟨q, hq⟩ := producer_of_warp hpre hc hWarp
    subst h
    exact ⟨(q, ⟨z.block / 4, Nat.lt_succ_of_le hBound⟩),
      r, j, f, z, extra, hr, hid, hf, hz, hSite, hSlot, rfl, hOrder⟩
  let key (p : records) : Key := (assign p).choose
  have hInj : Function.Injective key := by
    intro p q hEq
    obtain ⟨r, j, f, z, extra, hr, hid, hf, hz, hSite, hSlot, hUse, _⟩ := (assign p).choose_spec
    obtain ⟨s, j', f', z', extra', hs', hsid, hf', hz', hSite', hSlot', hUse', _⟩ :=
      (assign q).choose_spec
    change key p = key q at hEq
    change z.block / 4 = (key p).2.val at hUse
    change z'.block / 4 = (key q).2.val at hUse'
    let h := producerThread L cta (key p).1
    have hThread : producerThread L cta (key q).1 = h := by rw [← hEq]
    change s.id = .thread (producerThread L cta (key q).1, j') at hsid
    change X.get (producerThread L cta (key q).1, j') = some f' at hf'
    change Frame.stateAt (Machine.code P L) X (producerThread L cta (key q).1) j' =
      some (some (.index z')) at hz'
    rw [hThread] at hsid hf' hz'
    rw [← hEq] at hUse'
    have hh := Frame.lt_of_get hX hf
    have hSame := ready_same_block_unique hpre hX (hs h hh).machine hf hf' hz hz' hSite hSite'
      (by omega : z.block = z'.block)
    rw [hSame] at hid
    exact Subtype.ext (hX.object_index_eq hr hs' (hid.trans hsid.symm))
  have hOnto : Function.Surjective key := by
    by_contra hMissing
    have hh := Fintype.card_lt_of_injective_not_surjective key hInj hMissing
    rw [Fintype.card_coe, hCard] at hh
    simp only [Key, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] at hh
    exact (Nat.lt_irrefl _ hh)
  let use : Fin (n + 1) := ⟨n, Nat.lt_succ_self _⟩
  obtain ⟨p, hp⟩ := hOnto (lane, use)
  have hFit : Fits p (key p) := (assign p).choose_spec
  rw [hp] at hFit
  obtain ⟨r, j, f, z, extra, hr, hid, hf, hz, hSite, hSlot, hUse, hOrder⟩ := hFit
  change z.block / 4 = d.block / 4 at hUse
  exact ⟨j, f, z, extra, hf, hz, hSite, by omega, hOrder⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
