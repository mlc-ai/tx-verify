-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.BarOrd
public import Kernels.InklingRelDecode.Proof2.Lib.BarEarlyMember
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts
public import Kernels.InklingRelDecode.Proof.Interface.CopyFacts
public import Lemmas.Step.CtaBarNamed

@[expose] public section

/-!
# The Tensor Memory base word: the synchronization of the common start

The base word `[sharedBase, sharedBase + 4)` is written once, by lane 0 of warp 0 as the second
sub-step of `tcgen05.alloc` (a thread event of the model, `DStart.Site.allocWr`), and read by the
`ld.shared` that every one of the CTA's 256 threads executes between the two `bar.sync 0` of the
common start (`DStart.Site.ld0`, `Worker.Site.ld0`). The first four bytes of K slot 0 overlap it:
the first tensor copy into the K ring is issued after the second `bar.sync 0` by its thread.

The chain of the model is

1. the allocation's store, then, in its thread's program order, the thread's `bar.sync 0` of
   source ordinal 0;
2. every thread's `bar.sync 0` of ordinal 0 synchronizes with every other thread's
   (`NamedBar.early_same_ordinal_baseCausality`, with the arrivals of ordinal 0 and 1 the common
   start's, `Bar.earlySources_bar0`): the allocation's store is before every thread's read;
3. every thread's read is before the thread's `bar.sync 0` of ordinal 1, which synchronizes with
   every thread's own: every read of the word is before every event a thread executes after its
   second `bar.sync 0`, among them every tensor copy's issue (a copy's thread has made two
   barrier-0 arrivals: the prologue's and the loader's copy sites are not common-start sites).

What this file proves is steps 2 and 3 as `baseCausality` statements between the events
(`allocStore_baseCausality_read`, `read_baseCausality_copyIssue`,
`allocStore_baseCausality_copyIssue`); the issue of a copy is before its asynchronous writes
(`AsyncBefore`), which is the thread layer's part of the Tensor Core and TMA protocol.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Counting barrier-0 events along a trace -/

/-- An earlier barrier-0 event adds one to the count of a longer prefix. -/
theorem take_count_lt {l : List Event} {j k : Nat} {e : Event} (hj : l[j]? = some e)
    (hq : Execution.isBarId 0 e = true) (hjk : j < k) :
    (l.take j).countP (Execution.isBarId 0) + 1 ≤ (l.take k).countP (Execution.isBarId 0) := by
  have h1 := countP_succ hj
  simp only [hq, ↓reduceIte] at h1
  have h2 := (List.take_sublist_take_left (l := l) (show j + 1 ≤ k by omega)).countP_le
    (p := Execution.isBarId 0)
  omega

/-- **A non-barrier event whose prefix has at most `φ` barrier-0 events is before every
barrier-0 event of ordinal `φ`.** -/
theorem before_lt {l : List Event} {φ before i : Nat} {ev e : Event}
    (hc : (l.take before).countP (Execution.isBarId 0) ≤ φ) (hbev : l[before]? = some ev)
    (hnb : ¬ Execution.isBarId 0 ev = true) (hi : l[i]? = some e)
    (hq : Execution.isBarId 0 e = true) (hord : (l.take i).countP (Execution.isBarId 0) = φ) :
    before < i := by
  by_contra hle
  rcases Nat.lt_or_eq_of_le (Nat.not_lt.mp hle) with hlt | heq
  · have := take_count_lt hi hq hlt
    omega
  · subst heq
    rw [hi] at hbev
    cases hbev
    exact hnb hq

/-- **A thread with `r + 1` barrier-0 events before its event `k` has its arrival of ordinal `r`
before it**, for an early ordinal: a `bar.sync 0` without a count. -/
theorem arrival_before (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {h k r : Nat} (hr : r < ((X.tr h).take k).countP (Execution.isBarId 0)) (hr1 : r ≤ 1) :
    ∃ j pc, j < k ∧ X.IsBarrier (h, j) 0 none pc ∧
      ((X.tr h).take j).countP (Execution.isBarId 0) = r := by
  obtain ⟨j, e, hj, hq, hcnt⟩ := NamedBar.exists_ordinal (Execution.isBarId 0) _ hr
  rw [List.getElem?_take] at hj
  split at hj
  · rename_i hjk
    obtain ⟨pc, cnt, m, rfl⟩ := NamedBar.isBarId_form hq
    rw [List.take_take, Nat.min_eq_left (by omega)] at hcnt
    have hget : X.get (h, j) = some ⟨pc, .bar 0 cnt m⟩ := hj
    have hnone := bar0_count_none hX hS ht hget (by omega)
    subst hnone
    exact ⟨j, pc, hjk, hX.isBarrier_of_arrival noBarArrive ⟨m, hget⟩, hcnt⟩
  · cases hj

/-- **An exiting thread has made two barrier-0 arrivals.** -/
theorem exit_arrivals (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g j pc r : Nat} (he : X.get (g, j) = some ⟨pc, .exit⟩) (hr : r ≤ 1) :
    ∃ i pc', X.IsBarrier (g, i) 0 none pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId 0) = r := by
  have hj : j ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega
  have h2 : 2 ≤ ((X.tr g).take j).countP (Execution.isBarId 0) := by
    rcases exit_event_state hX hS ht he with ⟨d, hσ, -⟩ | ⟨x, hσ, -⟩
    · exact bar0_ordinal_two hX hS hj hσ (by simp [tLb_epi])
    · exact bar0_ordinal_two hX hS hj hσ (by simp [tLb_exit])
  obtain ⟨i, pc', -, hb, hc⟩ := arrival_before hX hS ht (h := g) (k := j) (r := r) (by omega) hr
  exact ⟨i, pc', hb, hc⟩

/-! ### Every thread has the early arrival a passed thread passed -/

/-- The constants of barrier 0's group: 8 warps without a thread count. -/
theorem bar0_group (hpre : Pre Q L mem0) :
    0 < CtaBarrier.warps L.block ∧ CtaBarrier.target L.block none = .ok (CtaBarrier.warps L.block) ∧
      (Finset.range (CtaBarrier.warps L.block)).card = CtaBarrier.warps L.block ∧
      ∀ w ∈ Finset.range (CtaBarrier.warps L.block), w < L.block / 32 := by
  have hb : L.block = 256 := hpre.block
  refine ⟨by simp [CtaBarrier.warps, hb], rfl, Finset.card_range _, fun w hw => ?_⟩
  simp only [Finset.mem_range, CtaBarrier.warps, hb] at hw ⊢
  omega

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
include hpre hX hS ht

/-- **Every thread of the CTA has the early arrival on barrier 0 that a passed thread passed.** -/
theorem bar0_member {h jf pcf g : Nat} (hf : X.IsBarrier (h, jf) 0 none pcf)
    (hpassed : jf + 1 < (X.tr h).length) (hn : ((X.tr h).take jf).countP (Execution.isBarId 0) ≤ 1)
    (hcta : g / L.block = h / L.block) :
    ∃ i pc, X.IsBarrier (g, i) 0 none pc ∧ ((X.tr g).take i).countP (Execution.isBarId 0) =
      ((X.tr h).take jf).countP (Execution.isBarId 0) := by
  obtain ⟨hpos, hcount, hcard, hbound⟩ := bar0_group hpre
  have hb : L.block = 256 := hpre.block
  refine NamedBar.early_member_arrival hX hpos hcount hcard hbound (by decide)
    (earlySources_bar0 hpre hX hS ht) hf hpassed hn hcta ?_ ?_
  · have := Nat.mod_lt g (show L.block > 0 by omega)
    simp only [Finset.mem_range, CtaBarrier.warps, hb] at this ⊢
    omega
  · rintro ⟨j, pcx, hex⟩
    exact exit_arrivals hX hS ht hex hn

/-! ### The chain -/

/-- **Two threads of one CTA synchronize through their early `bar.sync 0` of one ordinal.** An
event of `g` whose prefix has at most `φ` barrier-0 events and that is no barrier event is before
every event of `h` after `h`'s arrival of ordinal `φ ≤ 1`. -/
theorem bar0_chain {g h before after jf pcf : Nat} (hsame : SameCta L g h)
    (hf : X.IsBarrier (h, jf) 0 none pcf) (hφ : ((X.tr h).take jf).countP (Execution.isBarId 0) ≤ 1)
    (hbc : ((X.tr g).take before).countP (Execution.isBarId 0) ≤
      ((X.tr h).take jf).countP (Execution.isBarId 0)) (hbl : before < (X.tr g).length)
    (hbn : ∀ ev, (X.tr g)[before]? = some ev → ¬ Execution.isBarId 0 ev = true)
    (hafter : jf < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) := by
  have hpassed : jf + 1 < (X.tr h).length := by omega
  obtain ⟨i, pc, hi, hord⟩ := bar0_member hpre hX hS ht hf hpassed hφ hsame.2.2
  obtain ⟨ev, hev⟩ : ∃ ev, (X.tr g)[before]? = some ev := ⟨_, List.getElem?_eq_getElem hbl⟩
  have hgi : (X.tr g)[i]? = some ⟨pc, .bar 0 none .sync⟩ := hi
  have hlt : before < i := before_lt (φ := ((X.tr h).take jf).countP (Execution.isBarId 0))
    hbc hev (hbn ev hev) hgi (by simp [Execution.isBarId]) hord
  obtain ⟨hpos, hcount, hcard, hbound⟩ := bar0_group hpre
  exact NamedBar.early_same_ordinal_baseCausality hX hpos hcount hcard hbound (by decide)
    (earlySources_bar0 hpre hX hS ht) hsame hi hf hpassed hord hφ hlt hafter hlen

/-! ### The base word's events -/

omit hpre hX hS ht in
/-- The state before event `k` of thread `g` is the allocation's address store: lane 0 of warp 0,
the second sub-step of `tcgen05.alloc` (`DStart.Site.allocWr`). -/
def AllocStoreAt (Q : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∃ tm, St Q L X g k = some (some (.d (.dstart ⟨.allocWr, tm⟩)))

omit hpre hX hS ht in
/-- The state before event `k` of thread `g` is the load of the base word: the default
partition's (`DStart.Site.ld0`) or a worker's (`Worker.Site.ld0`). -/
def BaseReadAt (Q : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  (∃ tm, St Q L X g k = some (some (.d (.dstart ⟨.ld0, tm⟩)))) ∨
  (∃ P, St Q L X g k = some (some (.w (.worker ⟨.ld0, P⟩))))

omit hpre hX hS ht in
/-- The event at a common-start site that is no barrier has exactly the site's number of earlier
barrier-0 events and is no barrier event. -/
theorem start_facts (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {s : TSt}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some s)) (hl : tLb s < 2)
    (hi : tInc s = 0) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = tLb s ∧
      ∀ ev, (X.tr g)[k]? = some ev → ¬ Execution.isBarId 0 ev = true := by
  refine ⟨(ordinal_inv hX hS k s hk.le hσ).2 hl, fun ev hev hb => ?_⟩
  have he : X.get (g, k) = some ev := hev
  rcases start_event hX hS he hσ hl with ⟨h1, -⟩ | ⟨-, h⟩
  · omega
  · obtain ⟨pc, cnt, m, rfl⟩ := NamedBar.isBarId_form hb
    exact h 0 cnt m rfl

omit hpre hX hS ht in
theorem allocStore_facts (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat}
    (hk : k < (X.tr g).length) (h : AllocStoreAt Q L X g k) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = 0 ∧
      ∀ ev, (X.tr g)[k]? = some ev → ¬ Execution.isBarId 0 ev = true := by
  obtain ⟨tm, hσ⟩ := h
  exact start_facts hX hS hk hσ (by show 0 < 2; decide) rfl

omit hpre hX hS ht in
theorem baseRead_facts (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat}
    (hk : k < (X.tr g).length) (h : BaseReadAt Q L X g k) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = 1 ∧
      ∀ ev, (X.tr g)[k]? = some ev → ¬ Execution.isBarId 0 ev = true := by
  rcases h with ⟨tm, hσ⟩ | ⟨P, hσ⟩
  · exact start_facts hX hS hk hσ (by show 1 < 2; decide) rfl
  · exact start_facts hX hS hk hσ (by show 1 < 2; decide) rfl

/-! ### Steps 2 and 3 of the chain -/

/-- **The allocation's store is before every thread's read of the base word.** -/
theorem allocStore_baseCausality_read {g k h kr : Nat} (hsame : SameCta L g h)
    (hk : k < (X.tr g).length) (ha : AllocStoreAt Q L X g k) (hr : kr < (X.tr h).length)
    (hb : BaseReadAt Q L X h kr) :
    baseCausality L X (g, k) (h, kr) := by
  obtain ⟨hc0, hn0⟩ := allocStore_facts hX hS hk ha
  obtain ⟨hc1, -⟩ := baseRead_facts hX hS hr hb
  obtain ⟨j0, pc0, hj0, hf, hord⟩ := arrival_before hX hS ht (h := h) (k := kr) (r := 0)
    (by omega) (by omega)
  exact bar0_chain hpre hX hS ht hsame hf (by omega) (by omega) hk hn0 hj0 hr

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
