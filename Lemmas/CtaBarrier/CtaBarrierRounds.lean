-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierHistory

@[expose] public section

namespace PTX.CtaBarrier

/-- A proof invariant for programs using one full-CTA barrier resource for a fixed
number of rounds. `counts` is derived from actual warp arrival records. This is a
sufficient protocol in Lemmas, not a restriction on Core barrier histories. -/
structure RoundState (block rounds : Nat) (counts : Nat → Nat) (s : State) : Prop where
  arrived : (s.slots 0).arrived ⊆ Finset.range (warps block)
  expected : (s.slots 0).expected =
    if (s.slots 0).arrived = ∅ then none else some (warps block)
  count : ∀ w < warps block, counts w =
    (s.slots 0).generation + if w ∈ (s.slots 0).arrived then 1 else 0
  bound : ∀ w < warps block, counts w ≤ rounds
  exited : ∀ g ∈ s.exited, counts (g / 32) = rounds

theorem warps_pos {block : Nat} (hb : 0 < block) : 0 < warps block := by
  unfold warps
  omega

/-- Exiting after the final round cannot replace a missing arrival in an earlier
round. Thus an active full-CTA resource completes exactly when all warp slots arrived. -/
theorem RoundState.complete_iff {block rounds : Nat} {counts : Nat → Nat} {s : State}
    (hs : RoundState block rounds counts s) (hb : 0 < block) :
    complete block s.exited (s.slots 0) = true ↔
      Finset.range (warps block) ⊆ (s.slots 0).arrived := by
  classical
  by_cases he : (s.slots 0).arrived = ∅
  · have hn : ¬ Finset.range (warps block) ⊆ (s.slots 0).arrived := by
      intro h
      have hm := h (Finset.mem_range.mpr (warps_pos hb))
      rw [he] at hm
      exact Finset.notMem_empty 0 hm
    simp [complete,hs.expected,he,Nat.ne_of_gt (warps_pos hb)]
  have hg : (s.slots 0).generation < rounds := by
    obtain ⟨w,hw⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hwlt := Finset.mem_range.mp (hs.arrived hw)
    have hbound := hs.bound w hwlt
    rw [hs.count w hwlt,ite_eq_left hw] at hbound
    omega
  have all : allArrived block s.exited (s.slots 0) →
      Finset.range (warps block) ⊆ (s.slots 0).arrived := by
    intro ha w hw
    have hwlt := Finset.mem_range.mp hw
    by_cases hl : warpLive block s.exited w
    · exact ha w hw hl
    by_contra hm
    have hw0 : w * 32 < block := by unfold warps at hwlt; omega
    have hdead : w * 32 ∈ s.exited := by
      by_contra hn
      apply hl
      exact ⟨0,by simp,by simpa using hw0,by simpa using hn⟩
    have hc := hs.exited (w * 32) hdead
    have hdiv : w * 32 / 32 = w := by omega
    rw [hdiv,hs.count w hwlt,ite_eq_right hm] at hc
    omega
  simp only [complete,hs.expected,ite_eq_right he]
  simp only [decide_eq_true_eq]
  constructor
  · rintro (hc | ⟨_,ha⟩)
    · have hcard : (Finset.range (warps block)).card ≤ (s.slots 0).arrived.card := by
        simpa using hc
      rw [Finset.eq_of_subset_of_card_le hs.arrived hcard]
    · exact all ha
  · intro ha
    exact .inl (by simpa using Finset.card_le_card ha)

/-- Changing unrelated resources does not affect this protocol invariant. -/
theorem RoundState.congr {block rounds : Nat} {counts : Nat → Nat} {s t : State}
    (hs : RoundState block rounds counts s) (hslot : t.slots 0 = s.slots 0)
    (hexit : t.exited = s.exited) : RoundState block rounds counts t := by
  constructor
  · simpa only [hslot] using hs.arrived
  · simpa only [hslot] using hs.expected
  · simpa only [hslot] using hs.count
  · exact hs.bound
  · simpa only [hexit] using hs.exited

/-- Settling a full round preserves every warp's recorded arrival count. -/
theorem RoundState.settle {block rounds : Nat} {counts : Nat → Nat} {s : State}
    (hs : RoundState block rounds counts s) (hb : 0 < block) :
    RoundState block rounds counts
      {s with slots := fun id => if id = 0 then CtaBarrier.settle block s.exited (s.slots 0)
        else s.slots id} := by
  classical
  by_cases hc : complete block s.exited (s.slots 0) = true
  · have hall := (hs.complete_iff hb).mp hc
    have hmem : ∀ w < warps block, w ∈ (s.slots 0).arrived :=
      fun w hw => hall (Finset.mem_range.mpr hw)
    constructor
    · simp [settle_complete hc]
    · simp [settle_complete hc]
    · intro w hw
      simpa [settle_complete hc,hmem w hw] using hs.count w hw
    · exact hs.bound
    · exact hs.exited
  · have hf : complete block s.exited (s.slots 0) = false := by
      cases h : complete _ _ _ <;> simp_all
    exact hs.congr (by simp [settle_pending hf]) rfl

/-- Initial resources have no recorded arrivals. -/
theorem RoundState.initial (block rounds : Nat) :
    RoundState block rounds (fun _ => 0) {} := by
  constructor <;> simp

/-- A full-CTA arrival's pre-update state exposes its actual generation. -/
theorem arrive_full_shape {block warp : Nat} {s t : State}
    (h : CtaBarrier.arrive block s 0 warp none = .ok t) :
    warp < warps block ∧ warpLive block s.exited warp ∧ warp ∉ (s.slots 0).arrived ∧
    t.exited = s.exited ∧ t.slots 0 = CtaBarrier.settle block s.exited
      {s.slots 0 with
        expected := some (warps block), arrived := insert warp (s.slots 0).arrived} := by
  by_cases hw : warp < warps block ∧ warpLive block s.exited warp
  · by_cases ha : warp ∈ (s.slots 0).arrived
    · simp [arrive,hw,target,ha,bind,Except.bind,pure,Except.pure,throw] at h
    · cases he : (s.slots 0).expected with
      | none =>
        simp [arrive,hw,target,ha,he] at h
        obtain rfl := h.symm
        exact ⟨hw.1,hw.2,ha,rfl,by simp⟩
      | some n =>
        by_cases hn : n = warps block
        · simp [arrive,hw,target,ha,he,hn,bind,Except.bind,pure,Except.pure] at h
          obtain rfl := h.symm
          exact ⟨hw.1,hw.2,ha,rfl,by simp⟩
        · simp [arrive,hw,target,ha,he,hn,bind,Except.bind,pure,Except.pure] at h
  · simp [arrive,hw,bind,Except.bind,pure,Except.pure,throw] at h

/-- Increment only the warp that actually arrived. -/
def increment (counts : Nat → Nat) (warp : Nat) : Nat → Nat :=
  fun w => if w = warp then counts w + 1 else counts w

/-- The raw arrival increments one count; settling then advances the shared round
only when every warp has arrived. No source ordinal is assumed by this lemma. -/
theorem RoundState.arrive {block rounds warp : Nat} {counts : Nat → Nat} {s t : State}
    (hs : RoundState block rounds counts s) (hb : 0 < block)
    (hbound : counts warp < rounds) (h : CtaBarrier.arrive block s 0 warp none = .ok t) :
    RoundState block rounds (increment counts warp) t := by
  classical
  obtain ⟨hw,hl,ha,he,ht⟩ := arrive_full_shape h
  let u : State :=
    { s with slots := fun slotId =>
        if slotId = 0 then
          {s.slots 0 with
            expected := some (warps block), arrived := insert warp (s.slots 0).arrived}
        else s.slots slotId }
  have hu : RoundState block rounds (increment counts warp) u := by
    constructor
    · simpa only [u,↓reduceIte] using Finset.insert_subset (Finset.mem_range.mpr hw) hs.arrived
    · simp [u]
    · intro w hw'
      by_cases heq : w = warp
      · subst w
        simp [u,increment,hs.count warp hw,ha]
      · simp only [u,↓reduceIte,increment,Finset.mem_insert,heq,false_or]
        exact hs.count w hw'
    · intro w hw'
      by_cases heq : w = warp
      · subst w; simpa [increment] using Nat.succ_le_of_lt hbound
      · simpa only [increment,ite_eq_right heq] using hs.bound w hw'
    · intro g hg
      have hne : g / 32 ≠ warp := by
        intro hgw
        have hc := hs.exited g hg
        rw [hgw] at hc
        omega
      simpa only [increment,ite_eq_right hne] using hs.exited g hg
  apply (hu.settle hb).congr
  · simpa only [u,↓reduceIte] using ht
  · exact he

/-- The pre-arrival count equals the actual resource generation. -/
theorem RoundState.arrival_generation {block rounds warp : Nat} {counts : Nat → Nat}
    {s t : State} (hs : RoundState block rounds counts s)
    (h : CtaBarrier.arrive block s 0 warp none = .ok t) : counts warp = (s.slots 0).generation := by
  obtain ⟨hw,_,ha,_⟩ := arrive_full_shape h
  simpa only [ite_eq_right ha,Nat.add_zero] using hs.count warp hw

/-- An exit contributes no arrival. -/
theorem exit_shape {block g : Nat} {s t : State}
    (h : exitThread block s g = .ok t) :
    g < block ∧ g ∉ s.exited ∧ t.exited = insert g s.exited ∧
      t.slots 0 = CtaBarrier.settle block (insert g s.exited) (s.slots 0) := by
  by_cases hg : g < block ∧ g ∉ s.exited
  · simp [exitThread,hg,pure,Except.pure] at h
    obtain rfl := h.symm
    exact ⟨hg.1,hg.2,rfl,rfl⟩
  · simp [exitThread,hg,bind,Except.bind,throw] at h

/-- A thread exiting after its final round leaves arrival counts unchanged. -/
theorem RoundState.exit {block rounds g : Nat} {counts : Nat → Nat} {s t : State}
    (hs : RoundState block rounds counts s) (hb : 0 < block)
    (hcount : counts (g / 32) = rounds) (h : exitThread block s g = .ok t) :
    RoundState block rounds counts t := by
  classical
  obtain ⟨hg,hn,he,ht⟩ := exit_shape h
  let u : State := {s with exited := insert g s.exited}
  have hu : RoundState block rounds counts u := by
    refine ⟨hs.arrived,hs.expected,hs.count,hs.bound,?_⟩
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hcount
    · exact hs.exited f hf
  exact (hu.settle hb).congr (by simpa only [u,↓reduceIte] using ht) he

end PTX.CtaBarrier
