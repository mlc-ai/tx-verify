-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents
public import Lemmas.Kernel.Frame
import Lemmas.Flow.Resource
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The closing softmax barrier and its actual Tensor Memory release -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ScoreReleaseTrace

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 100000 in
private theorem resource_sites : OpPcsFast kernel.code tmemOp [91, 96, 1840] = true := by
  decide +kernel

/-- The frozen PTX has only CTA-group-one resource events, and its deallocation is the closing
softmax instruction. -/
theorem resource_source {i : EvId} {tag : Nat} {group : CtaGroup}
    {dst : Option Loc} {act : Tmem.Request}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get i = some ⟨tag, .tc (.resource group dst act)⟩) :
    group = .one ∧ (∀ base n, act = .dealloc base n → tag = 1840) := by
  rcases PTX.Flow.get_source hX he with ⟨_, h⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases h
  have hp := OpPcsFast.mem resource_sites hc (fires_resource_op hf rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_91)
    obtain ⟨_, hgroup, _, _, hact⟩ := fires_tcAlloc_resource hf rfl
    refine ⟨hgroup, ?_⟩
    intro base n h
    rw [hact] at h
    cases h
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_96)
    obtain ⟨hgroup, _, hact⟩ := fires_tcRelinquish_resource hf rfl
    refine ⟨hgroup, ?_⟩
    intro base n h
    rw [hact] at h
    cases h
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1840)
    exact ⟨(fires_tcDealloc_resource hf rfl).1, fun _ _ _ => rfl⟩

local macro "other_position" : tactic =>
  `(tactic| first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)
    | (rename_i a b c; revert a b c; decide)
    | (rename_i a b c d; revert a b c d; decide))

private theorem exit_of_position {g : Nat} {d : Machine.ThreadD}
    (h : (Machine.code P L g).pc d = 1840) :
    ∃ s, d = .wg0 s ∧ s.site = .exit := by
  cases d
  case wg0 d =>
    change d.site.pc = 1840 at h
    refine ⟨d, rfl, ?_⟩
    generalize hsite : d.site = s at h ⊢
    clear hsite d
    cases s
    case exit => rfl
    all_goals exfalso; revert h; other_position
  case prologue d =>
    change d.pc = 1840 at h
    exfalso
    cases d <;> revert h <;> other_position
  case mma d =>
    change d.site.pc = 1840 at h
    exfalso
    generalize hsite : d.site = s at h
    clear hsite d
    cases s <;> revert h <;> other_position
  case tma d =>
    change d.site.pc = 1840 at h
    exfalso
    generalize hsite : d.site = s at h
    clear hsite d
    cases s <;> revert h <;> other_position
  case index d =>
    change d.site.pc = 1840 at h
    exfalso
    generalize hsite : d.site = s at h
    clear hsite d
    cases s <;> revert h <;> other_position
  case wg2 d =>
    change d.site.pc = 1840 at h
    exfalso
    generalize hsite : d.site = s at h
    clear hsite d
    cases s <;> revert h <;> other_position
  case idle d =>
    change d.pc = 1840 at h
    exfalso
    cases d <;> revert h <;> decide
  case head => exact ((by decide : 1843 ≠ 1840) h).elim
  case done => exact ((by decide : 3611 ≠ 1840) h).elim

/-- Any actual deallocation in a followed trace is the warp-zero exit of WG0. -/
theorem dealloc_state_at_followed {g i tag base n : Nat} {group : CtaGroup}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (he : X.get (g, i) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧ d.site = .exit := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, _, hstate, hf⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine ht he (by simp)
  obtain ⟨t, ⟨ha, _⟩, hfire⟩ := hf
  have htag := (resource_source hX he).2 base n rfl
  have heq : tag = (Machine.code P L g).pc s := (fires_pc hfire).trans ha.1
  obtain ⟨d, rfl, hsite⟩ := exit_of_position (heq.symm.trans htag)
  exact ⟨d, hstate, hsite⟩

/-- Recover the deallocation state in a fully tracked trace. -/
theorem dealloc_state {g i tag base n : Nat} {group : CtaGroup}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    ∃ d, Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧ d.site = .exit :=
  dealloc_state_at_followed hX hs (ht g i (Frame.lt_of_get hX he)) he

set_option maxHeartbeats 1500000 in
private theorem role_exit_predecessor {g : Nat} {s d : Wg0.D} {e : Event}
    (hn : Wg0.next P L g s e = some (some d)) (hd : d.site = .exit) :
    s.site = .everyone := by
  cases hp : s.site <;> cases hk : e.kind <;>
    simp only [Wg0.next, Wg0.nextSite, hp, hk, Wg0.waitStep, Wg0.writeStep, reduceCtorEq] at hn
  case everyone.bar => rfl
  case maxRead.rd =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      cases hd
    · cases hn
  case rescaleVote.voteMode =>
    obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
    cases hd
  all_goals repeat' split at hn
  all_goals try (simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals cases hn
  all_goals try (simp only [Wg0.afterSink, Wg0.afterLen, Wg0.epiAfterBar] at hd)
  all_goals try split_ifs at hd
  all_goals try (simp [hp] at hd)
  all_goals unfold Wg0.afterScoreSite at hd
  all_goals split at hd <;> cases hd

theorem exit_predecessor {g : Nat} {s : Machine.ThreadD} {d : Wg0.D} {e : Event}
    (hn : Machine.next P L g s e = some (some (.wg0 d))) (hd : d.site = .exit) :
    ∃ q, s = .wg0 q ∧ q.site = .everyone := by
  cases s
  case wg0 q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i q' hnext
      cases hn
      exact ⟨q, rfl, role_exit_predecessor hnext hd⟩
    · split at hn <;> cases hn
    · cases hn
  case prologue st =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          change Wg0.firstSite P = Wg0.Site.exit at hd
          simp only [Wg0.firstSite, Wg0.afterSink, Wg0.afterLen] at hd
          split_ifs at hd
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

/-- An actual deallocation is immediately preceded in its lane by a returned closing sync. -/
theorem barrier_before_dealloc_at_followed {g i tag base n : Nat} {group : CtaGroup}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.stateAt (Machine.code P L) X g i ≠ some none)
    (he : X.get (g, i) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    ∃ j barrierTag d, j + 1 = i ∧
      X.get (g, j) = some ⟨barrierTag, .bar 12 none .sync⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧ d.site = .everyone := by
  obtain ⟨d, hd, hsite⟩ := dealloc_state_at_followed hX hs ht he
  cases i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ j =>
    have hl : j < (X.tr g).length := by have := PTX.len_of_get he; simp only at this; omega
    obtain ⟨e, hget⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hl⟩
    rw [Frame.stateAt_succ hget] at hd
    cases hp : Frame.stateAt (Machine.code P L) X g j with
    | none => simp [hp] at hd
    | some s =>
      cases s with
      | none => simp [hp] at hd; cases hd
      | some s =>
        rw [hp, Option.bind_some] at hd
        obtain ⟨q, rfl, hq⟩ := exit_predecessor hd hsite
        obtain ⟨o, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX hget)).fired_at hget hp
        have hcode : kernel.code[q.site.pc]? =
            some ⟨none, .barSyncN (.reg 2425) (.reg 2426) false⟩ := by
          rw [hq]
          exact Flow.code_1835
        obtain ⟨t, hat, hfire⟩ := RingGateEvents.fired_at_code hf hcode
        change (Wg0.code P L g).AtD q t at hat
        rw [Wg0.event_everyone hpre hat hq] at hfire
        exact ⟨j, _, q, rfl, hget.trans (congrArg some hfire.1), hp, hq⟩

/-- A deallocation's returned closing sync in a fully tracked trace. -/
theorem barrier_before_dealloc {g i tag base n : Nat} {group : CtaGroup}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    ∃ j barrierTag d, j + 1 = i ∧
      X.get (g, j) = some ⟨barrierTag, .bar 12 none .sync⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧ d.site = .everyone :=
  barrier_before_dealloc_at_followed hpre hX hs (ht g i (Frame.lt_of_get hX he)) he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ScoreReleaseTrace
