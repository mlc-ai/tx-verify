-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualFreeIssuers
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualFreePool
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnCount
import Lemmas.Order.OrderBaseCausality
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

@[expose] public section

/-! # An index consumer precedes all later producer uses of its slot -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem thread_of_cta_tid (hpre : Pre P L mem0) {a b : Nat}
    (hCta : ctaOf L a = ctaOf L b) (hTid : tidOf L a = tidOf L b) : a = b := by
  have hMod : a % L.block = b % L.block := by
    simpa only [tidOf_eq hpre, hpre.block] using hTid
  have hA := Nat.div_add_mod a L.block
  have hB := Nat.div_add_mod b L.block
  change a / L.block = b / L.block at hCta
  rw [hCta, hMod] at hA
  exact hA.symm.trans hB

private def BadReuse (P : Params) (L : Launch) (X : Execution)
    (read : EvId) (block : Nat) (p : EvId) : Prop :=
  ∃ (e : Event) (d : Wg1Index.D), X.get p = some e ∧
    Frame.stateAt (Machine.code P L) X p.1 p.2 = some (some (.index d)) ∧
    IndexProductionSite d.site ∧ ctaOf L p.1 = ctaOf L read.1 ∧
    d.block % 4 = block % 4 ∧ block / 4 < d.block / 4 ∧ ¬ baseCausality L X read p

/-- A gather return is either within the current use, or has a causal predecessor from
a later publication of this same slot. -/
def GatherReturnBound (P : Params) (L : Launch) (X : Execution)
    (read : EvId) (block leader : Nat) : Prop :=
  ∀ {a t tag : Nat},
    X.get (a, t) = some ⟨tag, .arrive (free L (ctaOf L read.1) (indexSlot block)) 0 1 true .cta⟩ →
    warpOf L a = 5 → ¬ baseCausality L X read (a, t) →
    a = leader ∧ (arrivals (free L (ctaOf L read.1) (indexSlot block)) ((X.tr a).take t) ≤
      block / 4 ∨ ∃ (w u : Nat) (v : Event) (z : Wg1Index.D) (extra : Bool),
        X.get (w, u) = some v ∧ Frame.stateAt (Machine.code P L) X w u = some (some (.index z)) ∧
        ctaOf L w = ctaOf L read.1 ∧ z.block % 4 = block % 4 ∧ z.site = .ready extra ∧
        block / 4 < z.block / 4 ∧ baseCausality L X (w, u) (a, t))

private theorem earlier_return {g i t tag : Nat} {m : Loc}
    (hGet : X.get (g, t) = some ⟨tag, .arrive m 0 1 true .cta⟩)
    (hNotBefore : ¬ baseCausality L X (g, i) (g, t)) : t ≤ i := by
  by_contra! hAfter
  have hNoAcc : (X.get (g, t)).bind Event.acc = none := by rw [hGet]; rfl
  exact hNotBefore (.single (.inl (po_of_not_access rfl hAfter (PTX.len_of_get hGet) hNoAcc)))

private theorem no_bad_reuse {g i block leader : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound)
    (hGather : GatherReturnBound P L X (g, i) block leader)
    (hReader : wgOf L g = 0 ∨ g = leader)
    (hCount : arrivals (free L (ctaOf L g) (indexSlot block)) ((X.tr g).take i) = block / 4) :
    ¬ ∃ p, BadReuse P L X (g, i) block p := by
  classical
  intro hBad
  obtain ⟨p, hp, hMin⟩ := causal_minimal_event hX (BadReuse P L X (g, i) block)
    (fun p h => by obtain ⟨f, _, hf, _⟩ := h; exact ⟨f, hf⟩) hBad
  obtain ⟨h, j⟩ := p
  obtain ⟨f, z, hf, hz, hProd, hCta, hSlot, hLater, hNotBefore⟩ := hp
  let n := block / 4
  let slot := indexSlot block
  let m := free L (ctaOf L g) slot
  have hSlot' : indexSlot z.block = slot := Fin.ext hSlot
  obtain ⟨records, hCard, hRecords⟩ := actual_producer_free_pool hpre hX hs hf hz hProd hLater
  rw [hCta, hSlot'] at hRecords
  let Key := Sum (Fin 128 × Fin (n + 1)) (Fin (n + 1))
  let SoftmaxBlock (a t : Nat) := (((X.tr a).drop (firstMaskStart P L X a)).take
    (t - firstMaskStart P L X a)).countP isProbabilityPublication
  let Fits (c : Key) (a t tag : Nat) : Prop :=
    match c with
    | .inl (lane, use) => ctaOf L a = ctaOf L g ∧ tidOf L a = lane.val ∧
        firstMaskStart P L X a ≤ t ∧ tag = Wg0.Site.validFree.pc ∧
        SoftmaxBlock a t % 4 = slot.val ∧ SoftmaxBlock a t / 4 = use.val
    | .inr use => a = leader ∧ arrivals m ((X.tr leader).take t) = use.val
  have assign (p : records) :
      ∃ c : Key, ∃ (r : Record Ref) (a t tag : Nat),
        (X.objects m)[p.val]? = some r ∧ r.id = .thread (a, t) ∧
        X.get (a, t) = some ⟨tag, .arrive m 0 1 true .cta⟩ ∧ Fits c a t tag := by
    obtain ⟨r, a, t, tag, hr, hId, hGet, hOrder⟩ := hRecords p.val p.property
    obtain ⟨hACta, hIssuer, _⟩ := actual_index_free_arrive hpre hX hs hGet rfl
    rcases hIssuer with ⟨hWg, hTag⟩ | ⟨hWarp, hTag⟩
    · obtain ⟨hStart, hAnchor⟩ :=
        first_mask_start_of_release hpre hX hs hGet hWg hTag rfl
      obtain ⟨b, hBlock, _, hKind, _⟩ :=
        actual_softmax_return_ordinal hpre hX hs hGet hStart hAnchor hTag
      have hB : b = SoftmaxBlock a t := hBlock
      have hAddr : m = free L (ctaOf L a) (indexSlot b) := (Kind.arrive.inj hKind).1
      have hBSlot : b % 4 = slot.val := (free_address hAddr).2.symm
      have hBU : b / 4 ≤ n := by
        by_contra! hU
        obtain ⟨w, u, v, wD, extra, hv, hw, hWCta, hWSlot, hWSite, hWUse, hWOrder⟩ :=
          actual_softmax_depends_on_later_producer hpre hX hs hGet hStart hAnchor hTag hBlock hU
        have hPast := hWOrder.trans hOrder
        apply hMin (w, u) hPast
        refine ⟨v, wD, hv, hw, .inl ⟨extra, hWSite⟩, hWCta.trans hACta,
          hWSlot.trans hBSlot, hWUse, ?_⟩
        exact fun h => hNotBefore (h.trans hPast)
      have hTid : tidOf L a < 128 := by unfold wgOf at hWg; omega
      refine ⟨.inl (⟨tidOf L a, hTid⟩, ⟨b / 4, by omega⟩), r, a, t, tag, hr, hId, hGet,
        hACta, rfl, hStart, hTag, ?_, ?_⟩
      · rw [← hB]; exact hBSlot
      · rw [← hB]
    · have hNo : ¬ baseCausality L X (g, i) (a, t) :=
        fun h => hNotBefore (h.trans hOrder)
      obtain ⟨hA, hc | ⟨w, u, v, dz, extra, hv, hw, hWCta, hWSlot, hWSite, hWUse, hPast⟩⟩ :=
        hGather hGet hWarp hNo
      · subst a
        exact ⟨.inr ⟨arrivals m ((X.tr leader).take t), Nat.lt_succ_of_le hc⟩, r, leader, t, tag,
          hr, hId, hGet, rfl, rfl⟩
      · exact (hMin (w, u) (hPast.trans hOrder) ⟨v, dz, hv, hw, .inl ⟨extra, hWSite⟩,
          hWCta, hWSlot, hWUse, fun h => hNo (h.trans hPast)⟩).elim
  let key (p : records) : Key := (assign p).choose
  have hInjective : Function.Injective key := by
    intro p q hKey
    obtain ⟨r, a, t, tag, hr, hid, hGet, hP⟩ := (assign p).choose_spec
    obtain ⟨s, b, u, tag', hS, hSid, hGet', hQ⟩ := (assign q).choose_spec
    change Fits (key p) a t tag at hP
    change Fits (key q) b u tag' at hQ
    rw [← hKey] at hQ
    have hId : (a, t) = (b, u) := by
      cases h : key p with
      | inl pair =>
        rw [h] at hP hQ
        obtain ⟨hACta, hATid, hAStart, hATag, hASlot, hAUse⟩ := hP
        obtain ⟨hBCta, hBTid, hBStart, hBTag, hBSlot, hBUse⟩ := hQ
        have hEq := thread_of_cta_tid hpre (hACta.trans hBCta.symm) (hATid.trans hBTid.symm)
        subst b
        rcases lt_trichotomy t u with hlt | rfl | hlt
        · have hStrict : SoftmaxBlock a t < SoftmaxBlock a u :=
            actual_softmax_return_count_lt hX hGet hGet' hATag hBTag hAStart hlt
          omega
        · rfl
        · have hStrict : SoftmaxBlock a u < SoftmaxBlock a t :=
            actual_softmax_return_count_lt hX hGet' hGet hBTag hATag hBStart hlt
          omega
      | inr use =>
        rw [h] at hP hQ
        obtain ⟨ha, hA⟩ := hP
        obtain ⟨hb, hB⟩ := hQ
        subst a
        subst b
        have hArrives (tag : Nat) : arrivesOn m ⟨tag, .arrive m 0 1 true .cta⟩ = true := by
          simp [arrivesOn, sourceArrive]
        unfold arrivals at hA hB
        rcases lt_trichotomy t u with hlt | rfl | hlt
        · have hCount := countP_take_succ hGet (hArrives tag)
          have hLe := countP_take_mono (arrivesOn m) (X.tr leader) (show t + 1 ≤ u by omega)
          omega
        · rfl
        · have hCount := countP_take_succ hGet' (hArrives tag')
          have hLe := countP_take_mono (arrivesOn m) (X.tr leader) (show u + 1 ≤ t by omega)
          omega
    exact Subtype.ext (hX.object_index_eq hr hS (hid.trans ((congrArg Ref.thread hId).trans
      hSid.symm)))
  have hOlder {t tag : Nat}
      (hGet : X.get (g, t) = some ⟨tag, .arrive m 0 1 true .cta⟩)
      (hOrder : baseCausality L X (g, t) (h, j)) :
      arrivals m ((X.tr g).take t) < n := by
    have hLe := earlier_return hGet (fun h => hNotBefore (h.trans hOrder))
    have hLt : t < i := lt_of_le_of_ne hLe (fun h => hNotBefore (h ▸ hOrder))
    have hStep := countP_take_succ hGet (show arrivesOn m ⟨tag, .arrive m 0 1 true .cta⟩ =
      true by simp [arrivesOn, sourceArrive])
    have hMono := countP_take_mono (arrivesOn m) (X.tr g) (show t + 1 ≤ i by omega)
    rw [hStep] at hMono
    change ((X.tr g).take i).countP (arrivesOn m) = n at hCount
    change ((X.tr g).take t).countP (arrivesOn m) < n
    omega
  have hNotOnto : ¬ Function.Surjective key := by
    intro hOnto
    let use : Fin (n + 1) := ⟨n, Nat.lt_succ_self _⟩
    rcases hReader with hWg | hLeader
    · let lane : Fin 128 := ⟨tidOf L g, by unfold wgOf at hWg; omega⟩
      obtain ⟨p, hp⟩ := hOnto (.inl (lane, use))
      obtain ⟨r, a, t, tag, hr, hid, hGet, hFit⟩ := (assign p).choose_spec
      change Fits (key p) a t tag at hFit
      rw [hp] at hFit
      obtain ⟨hCta, hTid, hStart, hTag, hSlot, hUse⟩ := hFit
      have hEq : a = g := thread_of_cta_tid hpre hCta hTid
      subst a
      have hBad := (hRecords p.val p.property)
      obtain ⟨r', a, t', _, hr', hid', _, hOrder⟩ := hBad
      obtain rfl := Option.some.inj (hr.symm.trans hr')
      obtain ⟨rfl, rfl⟩ := Ref.thread.inj (hid.symm.trans hid')
      obtain ⟨_, hAnchor⟩ := first_mask_start_of_release hpre hX hs hGet hWg hTag rfl
      have hBlock : indexSlot (SoftmaxBlock g t) = slot := Fin.ext hSlot
      have hLower := actual_softmax_return_count_le hpre hX hs hGet hStart hAnchor hTag
        (block := SoftmaxBlock g t) rfl
      rw [hBlock, hUse] at hLower
      exact (Nat.not_lt_of_ge hLower) (hOlder hGet hOrder)
    · obtain ⟨p, hp⟩ := hOnto (.inr use)
      obtain ⟨r, a, t, tag, hr, hid, hGet, hFit⟩ := (assign p).choose_spec
      change Fits (key p) a t tag at hFit
      rw [hp] at hFit
      obtain ⟨hA, hUse⟩ := hFit
      subst a
      subst leader
      obtain ⟨r', a, t', _, hr', hid', _, hOrder⟩ := hRecords p.val p.property
      obtain rfl := Option.some.inj (hr.symm.trans hr')
      obtain ⟨rfl, rfl⟩ := Ref.thread.inj (hid.symm.trans hid')
      exact (Nat.not_lt_of_ge hUse.ge) (hOlder hGet hOrder)
  have hBound := Fintype.card_lt_of_injective_not_surjective key hInjective hNotOnto
  rw [Fintype.card_coe, hCard] at hBound
  change (n + 1) * 129 < Fintype.card (Sum (Fin 128 × Fin (n + 1)) (Fin (n + 1))) at hBound
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hBound
  omega

/-- A consumer which still holds its slot precedes each later producer use. -/
theorem consumer_before_future_producer {g i h j block leader : Nat} {z : Wg1Index.D}
    {f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound)
    (hGather : GatherReturnBound P L X (g, i) block leader)
    (hReader : wgOf L g = 0 ∨ g = leader)
    (hCount : arrivals (free L (ctaOf L g) (indexSlot block)) ((X.tr g).take i) = block / 4)
    (hf : X.get (h, j) = some f)
    (hz : Frame.stateAt (Machine.code P L) X h j = some (some (.index z)))
    (hProd : IndexProductionSite z.site) (hCta : ctaOf L h = ctaOf L g)
    (hSlot : z.block % 4 = block % 4) (hLater : block / 4 < z.block / 4) :
    baseCausality L X (g, i) (h, j) := by
  by_contra hBad
  exact no_bad_reuse hpre hX hs hGather hReader hCount ⟨(h, j), f, z, hf, hz, hProd, hCta,
    hSlot, hLater, hBad⟩

variable {g i h j : Nat}

/-- A followed TMA event before its slot return precedes every later use of the slot. -/
theorem tma_before_future_producer {d : Wg1Tma.D} {z : Wg1Index.D} {e f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d))) (hBody : d.site ≠ .elect)
    (hReleased : TmaIndexTrace.released d = d.block) (hf : X.get (h, j) = some f)
    (hz : Frame.stateAt (Machine.code P L) X h j = some (some (.index z)))
    (hProd : IndexProductionSite z.site) (hCta : ctaOf L h = ctaOf L g)
    (hSlot : z.block % 4 = d.block % 4) (hLater : d.block / 4 < z.block / 4) :
    baseCausality L X (g, i) (h, j) := by
  let slot := indexSlot d.block
  let m := free L (ctaOf L g) slot
  have hg := Frame.lt_of_get hX he
  have hTrace := (hs g hg).machine.produces (hX.thr g hg)
  have hCount := TmaIndexTrace.composed_release_count hpre slot hTrace hd
  change arrivals m ((X.tr g).take i) = _ at hCount
  rw [hReleased] at hCount
  have hUse : (d.block + (3 - slot.val)) / 4 = d.block / 4 := by
    change (d.block + (3 - d.block % 4)) / 4 = d.block / 4
    omega
  rw [hUse] at hCount
  apply consumer_before_future_producer hpre hX hs (leader := g) (block := d.block)
    ?_ (.inr rfl) hCount hf hz hProd hCta hSlot hLater
  intro a t tag hGet hWarp hNo
  have hA := actual_tma_return_same_lane hpre hX hs hd hBody hGet hWarp rfl
  subst a
  exact ⟨rfl, .inl ((countP_take_mono (arrivesOn m) (X.tr g)
    (earlier_return hGet hNo)).trans_eq hCount)⟩

/-- A followed coordinate read precedes every later publication and overwrite of its slot. -/
theorem coordinate_before_future_producer {d : Wg1Tma.D} {z : Wg1Index.D} {e f : Event} {k : Fin 16}
    {sub : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coord k sub) (hf : X.get (h, j) = some f)
    (hz : Frame.stateAt (Machine.code P L) X h j = some (some (.index z)))
    (hProd : IndexProductionSite z.site) (hCta : ctaOf L h = ctaOf L g)
    (hSlot : z.block % 4 = d.block % 4) (hLater : d.block / 4 < z.block / 4) :
    baseCausality L X (g, i) (h, j) :=
  tma_before_future_producer hpre hX hs he hd (by simp [hSite])
    (by simp [TmaIndexTrace.released, TmaIndexTrace.begun, hSite]) hf hz hProd hCta hSlot hLater

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
