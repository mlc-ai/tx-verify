-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingConsumerControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadGuards
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

@[expose] public section

/-! # Recover the followed beginning of the concrete softmax ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def BeforeMaskReady (P : Params) (d : Wg0.D) : Prop :=
  Wg0.BeforeFirstQk P d ∧ d.site ≠ .qkDone ∧ d.site ≠ .maskReady

private theorem init_before_mask_ready : BeforeMaskReady P (Wg0.init P L g) := by
  refine ⟨Wg0.beforeFirstQk_init P L g, ?_⟩
  simp only [Wg0.init, Wg0.firstSite, Wg0.afterSink, Wg0.afterLen]
  split_ifs <;> decide

private theorem wg0_origin {q : Machine.ThreadD} {d : Wg0.D} {e : Event}
    (hn : Machine.next P L g q e = some (some (.wg0 d))) :
    d = Wg0.init P L g ∨
      ∃ old, q = .wg0 old ∧ Wg0.next P L g old e = some (some d) := by
  cases q
  case wg0 old =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i new hnext
      cases hn
      exact .inr ⟨old, rfl, hnext⟩
    · split at hn <;> cases hn
    · cases hn
  case prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          exact .inl rfl
        · cases hn
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem step_before_mask_ready {d next : Wg0.D} {e : Event}
    (hBefore : BeforeMaskReady P d) (hNext : Wg0.next P L g d e = some (some next)) :
    BeforeMaskReady P next ∨ (next.site = .maskReady ∧ next.block = 0) := by
  obtain ⟨⟨hBlock, hBefore⟩, hAfterQk, hMask⟩ := hBefore
  cases hSite : d.site <;> simp only [hSite] at hBefore
  case qkDone => exact (hAfterQk hSite).elim
  case maskReady => exact (hMask hSite).elim
  all_goals
    simp only [Wg0.next, Wg0.nextSite, hSite] at hNext
    repeat' split at hNext
  all_goals cases hNext
  all_goals
    simp only [BeforeMaskReady, Wg0.BeforeFirstQk, Wg0.init]
    simp_all only [Wg0.afterSink, Wg0.afterLen, and_true,
      ne_eq, reduceCtorEq, not_false_eq_true, and_self, true_and, true_or, or_true]
  all_goals (try split_ifs) <;> simp_all

section
variable {i : Nat}

/-- A followed WG0 state is still before the first mask poll or has the first block's
mask-poll state somewhere in its followed history. -/
private theorem followed_wg0_before_or_at_first_mask {d : Wg0.D} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) :
    BeforeMaskReady P d ∨
      ∃ start ≤ i, ∃ initial, initial.site = .maskReady ∧ initial.block = 0 ∧
        Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 initial)) := by
  induction i generalizing d with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ i ih =>
    have hBound : i < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hBound⟩
    obtain ⟨role, hState⟩ := FollowedPrefix.state_at hd (Nat.le_succ _)
    have hNext := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hState] at hNext
    rcases wg0_origin hNext.symm with rfl | ⟨old, rfl, hOld⟩
    · exact .inl init_before_mask_ready
    · rcases ih (Nat.le_of_lt hBound) hState with hBefore | ⟨j, hj, initial, hSite, hBlock, hFirst⟩
      · rcases step_before_mask_ready hBefore hOld with h | ⟨hSite, hBlock⟩
        · exact .inl h
        · exact .inr ⟨i + 1, le_rfl, d, hSite, hBlock, hd⟩
      · exact .inr ⟨j, by omega, initial, hSite, hBlock, hFirst⟩

/-- A dismissed WG0 lane has already reached its first block's mask acquire. -/
theorem dismissed_wg0_first_mask_ready {d : Wg0.D} {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hDismiss : Machine.next P L g (.wg0 d) e = some none) :
    ∃ start ≤ i, ∃ initial, initial.site = .maskReady ∧ initial.block = 0 ∧
      Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 initial)) := by
  rcases followed_wg0_before_or_at_first_mask (PTX.len_of_get he).le hd with hBefore | hFirst
  · exact (softmax_first_mask_prefix_next hpre hX hs he hd (.inl hBefore.1) hDismiss).elim
  · exact hFirst

/-- The actual first-block poll needed to interpret the concrete softmax loop's ordinals. -/
def FirstMaskAnchor (P : Params) (L : Launch) (X : Execution) (g start : Nat) : Prop :=
  ∃ initial : Wg0.D, initial.site = .maskReady ∧ initial.block = 0 ∧
    Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 initial))

/-- A followed output staging write has the first block's mask acquire in its prefix. -/
theorem first_mask_of_followed_stage {d : Wg0.D} {tile : Fin 4} {chunk : Fin 8}
    (hi : i ≤ (X.tr g).length) (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .oStage tile chunk) : ∃ start ≤ i, FirstMaskAnchor P L X g start := by
  rcases followed_wg0_before_or_at_first_mask hi hd with hEarly | hAnchor
  · have h := hEarly.1.2
    simp [hSite] at h
  · exact hAnchor

/-- A followed softmax closing gate has the first block's mask acquire in its prefix. -/
theorem first_mask_of_followed_closing {d : Wg0.D} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .everyone) : ∃ start ≤ i, FirstMaskAnchor P L X g start := by
  rcases followed_wg0_before_or_at_first_mask hi hd with hEarly | hAnchor
  · have h := hEarly.1.2
    simp [hSite] at h
  · exact hAnchor

/-- A followed tile barrier has the first block's mask acquire in its prefix. -/
theorem first_mask_of_followed_tile_bar {d : Wg0.D} {tile : Fin 4} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .epiBar tile) : ∃ start ≤ i, FirstMaskAnchor P L X g start := by
  rcases followed_wg0_before_or_at_first_mask hi hd with hEarly | hAnchor
  · have h := hEarly.1.2
    simp [hSite] at h
  · exact hAnchor

/-- The half-sum publish barrier has the first block's mask acquire in its prefix. -/
theorem first_mask_of_followed_sum_bar {d : Wg0.D} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hSite : d.site = .lseBar2)
    : ∃ start ≤ i, FirstMaskAnchor P L X g start := by
  rcases followed_wg0_before_or_at_first_mask hi hd with hEarly | hAnchor
  · have h := hEarly.1.2
    simp [hSite] at h
  · exact hAnchor

/-- A followed probability publisher has the first mask acquire in its prefix. -/
theorem first_mask_of_probability_publication {d : Wg0.D} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hSite : d.site = .soReady)
    : ∃ start ≤ i, FirstMaskAnchor P L X g start := by
  rcases followed_wg0_before_or_at_first_mask hi hd with hEarly | hAnchor
  · have h := hEarly.1.2
    simp [hSite] at h
  · exact hAnchor

/-- Every actual softmax return has the first block's followed mask poll in its prefix,
including returns after an earlier numerical dismissal. -/
theorem first_mask_anchor_of_release {e : Event} {m : Loc} {tx count : Nat} {release : Bool}
    {scope : MbarScope} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (he : X.get (g, i) = some e)
    (hWg : wgOf L g = 0) (hTag : e.pc = Wg0.Site.validFree.pc)
    (hKind : e.kind = .arrive m tx count release scope) :
    ∃ start ≤ i, FirstMaskAnchor P L X g start := by
  have hg := Frame.lt_of_get hX he
  rcases Frame.fired hs hX he with ⟨state, _, hd, hFire⟩ | ⟨_, _, _, hUb⟩
  · cases state with
    | some state =>
      have hSite := RingSourceSites.arrive_site hFire hKind
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
      cases state with
      | wg0 d =>
        have hp := Frame.event_pc hs hX he hd
        change e.pc = d.site.pc at hp
        have hFree : d.site = .validFree := by
          rcases hSite with h | h | h
          · rw [h, hTag] at hp
            cases hp
          · exact h
          · rw [h, hTag] at hp
            cases hp
        rcases followed_wg0_before_or_at_first_mask (PTX.len_of_get he).le hd with hBefore | hStart
        · exact (show False by simp [BeforeMaskReady, Wg0.BeforeFirstQk, hFree] at hBefore).elim
        · exact hStart
      | wg2 d => change wgOf L g = 2 at hRole; omega
      | mma _ => change warpOf L g = 4 at hRole; unfold wgOf warpOf at *; omega
      | tma _ => change warpOf L g = 5 at hRole; unfold wgOf warpOf at *; omega
      | index _ => change warpOf L g = 7 at hRole; unfold wgOf warpOf at *; omega
      | prologue _ | head | idle _ | done => exact hSite.elim
    | none =>
      obtain ⟨j, hj, d, f, hf, hState, hn⟩ := prior_dismissal (PTX.len_of_get he).le hd
      have hRole := RingRoleGeometry.of_trace hX hg (hs g hg).machine hState
      cases dismissal_is_consumer hpre hX hs hf hState hn with
      | wg0 d =>
        obtain ⟨start, hBefore, hAnchor⟩ := dismissed_wg0_first_mask_ready hpre hX hs hf hState hn
        exact ⟨start, by omega, hAnchor⟩
      | wg2 d => change wgOf L g = 2 at hRole; omega
  · rw [hUb] at hKind
    cases hKind
end

/-- Retain the concrete control registers of a followed mask acquire. -/
theorem softmax_mask_entry_facts {d : Wg0.D} {t : TState}
    (hSite : d.site = .maskReady) (hat : (Wg0.code P L g).AtD d t) :
    AtVector t 264 (softmaxMaskFacts L d.block (Wg0.blocksOf P L g)) t.sub t.acc := by
  have hpc := hat.1
  change t.pc = d.site.pc at hpc
  rw [hSite] at hpc
  refine ⟨hpc, rfl, rfl, hat.2.2.2.1, Wg0.reg974 hat hSite, Wg0.reg975 hat hSite, ?_, ?_, ?_⟩
  · have h := Wg0.reg_value hat (r := 477) (by rw [hSite]; decide +kernel)
    simpa [Wg0.valueOf, Wg0.table, Wg0.maskStride, sb, PTX.Flow.lookupLit] using h
  · have h := Wg0.reg_value hat (r := 981) (by rw [hSite]; decide +kernel)
    simpa [Wg0.valueOf, Wg0.table, Wg0.maskStride, sb, PTX.Flow.lookupLit] using h
  · apply holds_of_pointwise
    intro r hr
    simp only [softmaxLoopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Wg0.reg_value hat (r := 2883) (by rw [hSite]; decide +kernel)
    · exact Wg0.reg_value hat (r := 2884) (by rw [hSite]; decide +kernel)
    · exact Wg0.reg_value hat (r := 2952) (by rw [hSite]; decide +kernel)
    · exact Wg0.reg_value hat (r := 2953) (by rw [hSite]; decide +kernel)
    · exact Wg0.reg_value hat (r := 451) (by rw [hSite]; decide +kernel)
    · exact Wg0.reg_value hat (r := 452) (by rw [hSite]; decide +kernel)

/-- Replay the concrete suffix of a followed first mask acquire to any recorded return.
The slot ordinal is a count in the actual trace, and the preceding acquire has a real event id. -/
theorem actual_softmax_return_ordinal {start i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hStart : start ≤ i)
    (hAnchor : FirstMaskAnchor P L X g start) (hTag : e.pc = Wg0.Site.validFree.pc) :
    ∃ visit, visit = (((X.tr g).drop start).take (i - start)).countP isProbabilityPublication ∧
      visit < Wg0.blocksOf P L g ∧
      e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validFreeOff (visit % 4)⟩
        0 1 true .cta ∧
      ∃ q, start ≤ q ∧ q < i ∧ X.get (g, q) =
        some ⟨264, .wait ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validReadyOff (visit % 4)⟩
          (visit / 4 % 2) true true .cta⟩ ∧
        ∀ b < visit, ∃ j, start ≤ j ∧ j < q ∧ ∃ r, X.get (g, j) = some r ∧
          r.pc = Wg0.Site.validFree.pc ∧
          b = (((X.tr g).drop start).take (j - start)).countP isProbabilityPublication := by
  obtain ⟨d, hSite, hFirst, hState⟩ := hAnchor
  have hg := Frame.lt_of_get hX he
  let events := (X.tr g).drop start
  let k := i - start
  have hGet : events[k]? = some e := by
    change ((X.tr g).drop start)[i - start]? = _
    rw [List.getElem?_drop, Nat.add_sub_of_le hStart]
    exact he
  obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hState
    (List.ne_nil_of_mem (List.mem_of_getElem? hGet))
  have hAt : (Wg0.code P L g).AtD d t := hGood.1
  have hi := softmax_mask_entry_facts hSite hAt
  have hBatch := Wg1Mma.batchOf_lt hpre hg
  have hTotal : Wg0.blocksOf P L g < 2 ^ 31 := by
    have h := (Wg0.blocksOf_word_bounds hpre hBatch).2
    omega
  have hBlock : d.block < Wg0.blocksOf P L g := (show Wg0.Inv P L g d from hGood.2).blockLt
  have hShort : k < events.length := (List.getElem?_eq_some_iff.mp hGet).1
  have hSplit : events = events.take k ++ e :: events.drop (k + 1) := by
    have hDrop := List.drop_eq_getElem_cons hShort
    rw [(List.getElem?_eq_some_iff.mp hGet).2] at hDrop
    rw [← hDrop]
    exact (List.take_append_drop ..).symm
  change Run kernel Assumptions.all L g t events o at hRun
  rw [hSplit] at hRun
  obtain ⟨visit, hCount, hLe, hRelease, q, hq, hPoll, hVisits⟩ :=
    softmax_return_in_trace hpre hBlock hTotal hi hTag hRun
  rw [hFirst, Nat.zero_add] at hCount
  rw [← hSplit] at hPoll
  have hqk : q < k := lt_of_lt_of_le hq (List.length_take_le ..)
  refine ⟨visit, hCount, hLe, hRelease, start + q, by omega, by unfold k at hqk; omega, ?_, ?_⟩
  · change (X.tr g)[start + q]? = _
    simpa only [events, List.getElem?_drop] using hPoll
  · intro b hb
    obtain ⟨j, hj, r, hRead, hTag, hOrdinal⟩ := hVisits b (by omega) hb
    have hjk : j < k := hj.trans hqk
    refine ⟨start + j, by omega, by omega, r, ?_, hTag, ?_⟩
    · rw [List.getElem?_take, ite_eq_left hjk] at hRead
      change (X.tr g)[start + j]? = _
      simpa only [events, List.getElem?_drop] using hRead
    · rw [hFirst, Nat.zero_add, List.take_take, Nat.min_eq_left hjk.le] at hOrdinal
      simpa [events] using hOrdinal

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
