-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemAlloc
public import Lemmas.Protocol.MbarOneShot

@[expose] public section

/-! # The deallocation handshake

Before deallocating, each lane of warp 12 arrives once on the other CTA's handshake barrier
(`+320`, count 32) and waits at parity 0 on its own CTA's. The handshake barrier of CTA `cta` is
a one-phase barrier (`MbarOneShot.Hist`): its arrivals are the 32 lanes of warp 12 of the other
CTA of the pair (`hsArrivals`), one each, without transaction bytes; its polls are of parity 0
and nothing else operates on it (`TmemFacts`). So, with its initialization first (`HsInit`):

* no record of its history faults (`fault_free`);
* a successful wait of the CTA's warp 12 on it observes the arrival of every lane of the other
  CTA's warp 12 (`observes`): the hand-off that orders the other CTA's last events before this
  CTA's deallocation and exit.

`HsInit` is the barrier's initialization being its first record, without fault, and its only
one, with count 32 (`PairTmaRing.InitFirst`). The initialization does not happen before the
other CTA's arrivals: the start cluster barrier's arrival is relaxed and publishes it without
ordering it (`ClusterStart`). `InitFirst.deallocInit` proves `HsInit` from that publication
(`HsInitProof.hsInit`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.TmemAlloc
open PTX PTX.Proof AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The handshake barrier of CTA `cta`. -/
abbrev hsLoc (L : Launch) (cta : Nat) : Loc := FBar.loc L cta .dealloc

/-- Whether an event is an arrival on `m`. -/
def arrivesOn (m : Loc) (e : Event) : Bool :=
  match e.kind with
  | .arrive m' .. => decide (m' = m)
  | _ => false

theorem arrivesOn_true {m : Loc} {e : Event} (h : arrivesOn m e = true) :
    ∃ pc tx c rel sc, e = ⟨pc, .arrive m tx c rel sc⟩ := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp only [arrivesOn, decide_eq_true_eq, Bool.false_eq_true] at h
  subst h
  exact ⟨pc, _, _, _, _, rfl⟩

/-- The index of thread `g`'s first arrival on `m` (its trace's length if none). -/
def arriveIdx (X : Execution) (g : Nat) (m : Loc) : Nat := (X.tr g).findIdx (arrivesOn m)

/-- The arrivals the handshake barrier of CTA `cta` counts: lane `l` of warp 12 of the other CTA
of the pair, at its arrival, with no transaction bytes. -/
def hsArrivals (L : Launch) (X : Execution) (cta : Nat) : List (Ref × Nat) :=
  (List.range 32).map fun l =>
    (.thread (lane0 L (pairCta cta) + l, arriveIdx X (lane0 L (pairCta cta) + l) (hsLoc L cta)),
      0)

/-- **The handshake barrier is initialized first**, once, with count 32. -/
abbrev HsInit (L : Launch) (X : Execution) (cta : Nat) : Prop :=
  PairTmaRing.InitFirst X (hsLoc L cta) 32

theorem pairCta_pairCta (c : Nat) : pairCta (pairCta c) = c := by
  unfold pairCta
  omega

theorem hsArrivals_length (cta : Nat) : (hsArrivals L X cta).length = 32 := by
  simp [hsArrivals]

theorem hsArrivals_bytes (cta : Nat) : ((hsArrivals L X cta).map Prod.snd).sum = 0 := by
  simp only [hsArrivals, List.map_map]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx
  rfl

/-- An arrival on a handshake barrier is its thread's first. -/
theorem arriveIdx_eq (hX : Consistent L kernel asms mem0 X) (ht : TmemFacts L X)
    {g j pc tx c cta : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, j) = some ⟨pc, .arrive (hsLoc L cta) tx c rel sc⟩) :
    arriveIdx X g (hsLoc L cta) = j := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, -, -, -, huniq⟩ := ht.hs_arrive hg he rfl
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp he
  refine (List.findIdx_eq hlt).mpr ⟨?_, fun j' hj' => ?_⟩
  · rw [hget]
    simp [arrivesOn]
  · by_contra hp
    obtain ⟨pc', tx', c', rel', sc', hx⟩ := arrivesOn_true (Bool.not_eq_false _ ▸ hp)
    have h' : X.get (g, j') = some ⟨pc', .arrive (hsLoc L cta) tx' c' rel' sc'⟩ := by
      rw [← hx]
      exact List.getElem?_eq_getElem _
    have := huniq j' pc' tx' c' rel' sc' h'
    omega

/-- The event at a thread's handshake arrival index, if any, is an arrival on the barrier. -/
theorem get_arriveIdx {g : Nat} {m : Loc} {ev : Event}
    (he : X.get (g, arriveIdx X g m) = some ev) :
    ∃ pc tx c rel sc, ev = ⟨pc, .arrive m tx c rel sc⟩ := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp he
  have hp := List.findIdx_getElem (w := hlt)
  rw [← hget]
  exact arrivesOn_true hp

/-- A thread of warp 12 is a lane of its CTA's warp 12. -/
theorem lane_of_warp (hpre : Pre P L mem0) {g : Nat} (hw : warpOf L g = 12) :
    g = lane0 L (ctaOf L g) + g % 32 ∧ g % 32 < 32 := by
  unfold warpOf at hw
  unfold lane0 ctaOf
  rw [hpre.block] at hw ⊢
  have := Nat.div_add_mod g 512
  omega

/-- **The handshake barrier of CTA `cta` is a one-phase barrier** with the 32 arrivals of the
other CTA's warp 12. -/
theorem table (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : TmemFacts L X)
    {cta : Nat} (hi : HsInit L X cta) :
    MbarOneShot.Hist X (hsLoc L cta) (hsArrivals L X cta) [] where
  count := by
    rw [hsArrivals_length]
    simp only [validCount, limit]
    decide
  bytes := by rw [hsArrivals_bytes]; exact Nat.zero_le _
  sizes := by simp [hsArrivals_bytes]
  nodup := by simp
  arrivals_nodup := by
    simp only [hsArrivals, List.map_map]
    refine List.nodup_range.map fun a b h => ?_
    simp only [Function.comp_apply, Ref.thread.injEq, Prod.mk.injEq] at h
    omega
  records r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init hid he ha =>
      left
      obtain ⟨r0, h0, ha0, -, hu⟩ := hi r hr
      have hr0 := hu r hr ⟨_, ha⟩
      subst hr0
      rw [ha0, hsArrivals_length]
    | inval _ he _ => exact (ht.no_inval he).elim
    | @arrive g j pc tx c rel sc hid he ha =>
      right; left
      have hg := Frame.lt_of_get hX he
      obtain ⟨hw, hcta, rfl, rfl, -⟩ := ht.hs_arrive hg he rfl
      obtain ⟨hgl, hl⟩ := lane_of_warp hpre hw
      refine ⟨(.thread (g, j), 0), List.mem_map.mpr ⟨g % 32, List.mem_range.mpr hl, ?_⟩,
        hid, ha⟩
      have e1 : lane0 L (pairCta cta) + g % 32 = g := by
        rw [hcta, pairCta_pairCta]
        exact hgl.symm
      rw [e1, arriveIdx_eq hX ht he]
    | @wait g j pc p ok acq sc hid he ha =>
      right; right; right
      obtain ⟨-, -, rfl⟩ := ht.hs_wait (Frame.lt_of_get hX he) he rfl
      exact ⟨_, ok, hid, ha⟩
    | tensor _ he hm _ => exact (ht.hs_tensor he hm).elim
    | increment _ he _ => exact (ht.no_arriveOn he).elim
    | arriveOn _ he _ _ _ => exact (ht.no_arriveOn he).elim
    | bulk _ he _ _ _ => exact (ht.no_bulk he).elim
    | commit _ he htg _ => exact (ht.hs_commit he htg).elim
    | clc _ he _ _ _ => exact (ht.no_clc he).elim
  arrive_record r hr a ha hid := by
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    cases record_source hX.tma.2.2.1 hr with
    | @arrive g j pc tx c rel sc hid' he ha' =>
      obtain ⟨-, -, rfl, rfl, -⟩ := ht.hs_arrive (Frame.lt_of_get hX he) he rfl
      exact ha'
    | @init g j pc c hid' he _ | @inval g j pc hid' he _ | @wait g j pc _ _ _ _ hid' he _ =>
      rw [hid'] at hid
      simp only [Ref.thread.injEq, Prod.mk.injEq] at hid
      obtain ⟨rfl, rfl⟩ := hid
      obtain ⟨_, _, _, _, _, h⟩ := get_arriveIdx he
      cases h
    | tensor hid' _ _ _ => rw [hid'] at hid; cases hid
    | increment _ he _ => exact (ht.no_arriveOn he).elim
    | arriveOn _ he _ _ _ => exact (ht.no_arriveOn he).elim
    | bulk hid' _ _ _ _ => rw [hid'] at hid; cases hid
    | commit hid' _ _ _ => rw [hid'] at hid; cases hid
    | clc hid' _ _ _ _ => rw [hid'] at hid; cases hid
  init_first := by rw [hsArrivals_length]; exact hi
  copy_mbar c hc := by simp at hc
  no_inval v := fun ⟨_, he⟩ => ht.no_inval he

/-- No record of a handshake barrier's history faults. -/
theorem fault_free (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : TmemFacts L X) {cta : Nat} (hi : HsInit L X cta) {r : Record Ref}
    (hr : r ∈ X.objects (hsLoc L cta)) : r.fault = none :=
  (table hpre hX ht hi).fault_free hX hr

/-- **The handshake hands off**: a successful wait on CTA `cta`'s handshake barrier observes the
arrival of every lane `l` of the other CTA's warp 12. -/
theorem observes (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : TmemFacts L X) {cta : Nat} (hi : HsInit L X cta) {k : EvId}
    {pc : Nat} {acq : Bool} {ws : MbarScope}
    (he : X.get k = some ⟨pc, .wait (hsLoc L cta) 0 true acq ws⟩) {l : Nat} (hl : l < 32) :
    UpdateBeforeWait (X.objects (hsLoc L cta))
      (.thread (lane0 L (pairCta cta) + l,
        arriveIdx X (lane0 L (pairCta cta) + l) (hsLoc L cta))) (.thread k) :=
  (table hpre hX ht hi).observes_arrive hX
    (a := (.thread (lane0 L (pairCta cta) + l,
      arriveIdx X (lane0 L (pairCta cta) + l) (hsLoc L cta)), 0))
    (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩) he

end
end PTX.Kernels.FlashAttn4Fwd.Proof.TmemAlloc
