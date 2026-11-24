-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StateFields
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Flow.Final

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The probability stores and the proxy fence of an actual softmax publication -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ProbabilityRelease

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def BeforeSite (d : D) : Prop :=
  d.site = .soReady ∨ ∃ k, d.site = .pStore k ∧ 0 < 4 * k.val + d.sub

private def Predecessor (old d : D) : Prop :=
  (d.site = .soReady → old.site = .soFence ∧ old.block = d.block) ∧
  ∀ k, d.site = .pStore k → 0 < 4 * k.val + d.sub →
    ∃ q, old.site = .pStore q ∧ old.block = d.block ∧
      4 * q.val + old.sub + 1 = 4 * k.val + d.sub

set_option maxHeartbeats 3000000 in
private theorem role_previous {g : Nat} {d d' : D} {e : Event}
    (hInv : Inv P L g d) (hn : Wg0.next P L g d e = some (some d')) :
    Predecessor d d' := by
  cases hd : d.site <;> simp only [Wg0.next, nextSite, writeStep, waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hm
        simp [Predecessor]
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, hVote, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, hprob, rfl⟩ := Option.map_eq_some_iff.mp hm
      have hsubLt : d.sub < 1 := by simpa [hd, Site.elems] using hInv.subLt
      have hsub : d.sub = 0 := by omega
      have hOld := (vote_preserves_sub hVote).2
      have hNew := (probability_preserves_sub hprob).2
      simp [Predecessor, hNew, hOld, hsub]
    · cases hn
  case pStore k =>
    by_cases hk : k.val + 1 < 4 <;> simp only [hk, dite_true, dite_false] at hn
    all_goals
      have hsub : d.sub < 4 := by simpa [hd, Site.elems] using hInv.subLt
      repeat' split at hn
      all_goals cases hn
      all_goals constructor
      all_goals simp only [Site.elems] at *
      all_goals
        try solve
          | intro hready
            cases hready
          | intro q hq _
            cases hq
      all_goals
        intro q hq _
        have hq' := Site.pStore.inj hq
        subst q
        refine ⟨k, hd, trivial, ?_⟩
        first
        | rfl
        |
          change 4 * k.val + d.sub + 1 = 4 * (k.val + 1)
          omega
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp_all [Predecessor, Wg0.init, firstSite, afterSink, afterLen, afterScoreSite,
      epiAfterBar, loadOutput]
  all_goals repeat' split_ifs
  all_goals simp_all

private theorem prev_wg0 {g : Nat} {e : Event} {q : Machine.ThreadD} {d : D}
    (ho : ∀ old, q = .wg0 old → Inv P L g old)
    (hn : Machine.next P L g q e = some (some (.wg0 d))) (hd : BeforeSite d) :
    ∃ old : D, q = .wg0 old ∧ Predecessor old d := by
  cases q
  case prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        fin_cases w <;> split_ifs at hn <;> cases hn
        simp only [BeforeSite, Wg0.init, Wg0.firstSite, Wg0.afterSink, Wg0.afterLen] at hd
        repeat' split_ifs at hd
        all_goals simp_all
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  case wg0 old =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i st hnext
      cases hn
      exact ⟨old, rfl, role_previous (ho old rfl) hnext⟩
    · split at hn <;> cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem trace_previous {g i : Nat} {d : D} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : BeforeSite d) :
    ∃ j f old, i = j + 1 ∧ X.get (g, j) = some f ∧ Predecessor old d ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 old)) := by
  cases i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ j =>
    have hl : j < (X.tr g).length := by have := PTX.len_of_get he; simp only at this; omega
    have hf : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hl
    have hg := Frame.lt_of_get hX he
    obtain ⟨q, hq⟩ := FollowedPrefix.state_at hd (Nat.le_succ j)
    have hn := Frame.stateAt_succ (C := Machine.code P L) hf
    rw [hd, hq] at hn
    change some (some (.wg0 d)) = Machine.next P L g q (X.tr g)[j] at hn
    have ho : ∀ old, q = .wg0 old → Inv P L g old := by
      rintro old rfl
      obtain ⟨_, _, ⟨_, hi⟩, _⟩ := (hs.produces (hX.thr g hg)).fired_at hf hq
      exact hi
    obtain ⟨old, rfl, hp⟩ := prev_wg0 ho hn.symm hsite
    exact ⟨j, _, old, rfl, hf, hp, hq⟩

private theorem fired_fence {g : Nat} {d : D} {e : Event} {o : Option TState}
    (hd : d.site = .soFence) (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o) :
    e.kind = .fenceProxy (.async (some (.shared .cta))) none := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  have hp : d.site.pc = 1120 := by rw [hd]; rfl
  rw [hp, Flow.code_fenceProxy_0] at hf
  exact congrArg Event.kind hf.1

private theorem store_before_store {g : Nat} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (site sub : Fin 4) (rank : Nat) :
    ∀ {i : Nat} {d : D} {e : Event} {k : Fin 4},
      X.get (g, i) = some e →
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) →
      d.site = .pStore k →
      4 * site.val + sub.val + rank = 4 * k.val + d.sub →
      ∃ j ≤ i, ∃ q w, X.get (g, j) = some w ∧
        Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
        q.block = d.block ∧ q.site = .pStore site ∧ q.sub = sub.val := by
  induction rank with
  | zero =>
    intro i d e k he hd hk hr
    obtain ⟨_, _, ⟨_, hi⟩, _⟩ :=
      (hs.produces (hX.thr g (Frame.lt_of_get hX he))).fired_at he hd
    have hsub : d.sub < 4 := by simpa [hk, Site.elems] using hi.subLt
    have htSub := sub.isLt
    have hK : k = site := Fin.ext (by omega)
    exact ⟨i, le_rfl, d, e, he, hd, rfl, hk.trans (congrArg Site.pStore hK), by omega⟩
  | succ rank ih =>
    intro i d e k he hd hk hr
    have hpos : 0 < 4 * k.val + d.sub := by omega
    obtain ⟨j, w, q, hij, hw, hp, hq⟩ :=
      trace_previous hX hs he hd (.inr ⟨k, hk, hpos⟩)
    obtain ⟨l, hsite, hb, hnr⟩ := hp.2 k hk hpos
    obtain ⟨v, hv, z, ev, hev, hz, hzBlock, hzSite, hzSub⟩ :=
      ih hw hq hsite (by omega)
    exact ⟨v, by omega, z, ev, hev, hz, hzBlock.trans hb, hzSite, hzSub⟩

/-- An actual publication is immediately preceded by its proxy fence. Each selected packed
probability store of the same block occurs before that fence. -/
theorem actual_store_before_publication {g a : Nat} {out : D} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, a) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g a = some (some (.wg0 out)))
    (hsite : out.site = .soReady) (site sub : Fin 4) :
    ∃ f ft, a = f + 1 ∧ X.get (g, f) = some ⟨ft, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      ∃ j < f, ∃ d w u, X.get (g, j) = some w ∧
        Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧
        d.block = out.block ∧ d.site = .pStore site ∧ d.sub = sub.val ∧
        (Wg0.code P L g).toMachine.Fired (some d) w (some u) := by
  obtain ⟨f, vf, df, ha, hf, hprev, hdf⟩ := trace_previous hX hs he hd (.inl hsite)
  obtain ⟨hFence, hBlock⟩ := hprev.1 hsite
  obtain ⟨_, hfireFence⟩ := RingEvents.fired_of_trace hX hs hf hdf
  have hKind := fired_fence hFence hfireFence
  have hg := Frame.lt_of_get hX hf
  obtain ⟨last, hlf, dl, el, hdl, hbl, hkl, hsl, hel, _⟩ :=
    Wg0ProbabilityHistory.last_before_fence hX hg hs hdf hFence
  obtain ⟨_, _, ⟨_, hInv⟩, _⟩ := (hs.produces (hX.thr g hg)).fired_at hel hdl
  have hlim : dl.sub < 4 := by simpa [hkl, Site.elems] using hInv.subLt
  have hsub : dl.sub = 3 := by omega
  have hSS := site.isLt
  have hSU := sub.isLt
  have hr : 4 * site.val + sub.val + (15 - (4 * site.val + sub.val)) =
      4 * (3 : Fin 4).val + dl.sub := by rw [hsub]; omega
  obtain ⟨j, hj, d, w, hw, hstate, hbd, hsd, hsub'⟩ :=
    store_before_store hX hs site sub _ hel hdl hkl hr
  obtain ⟨o, hF⟩ := RingEvents.fired_of_trace hX hs hw hstate
  have hFGet : X.get (g, f) = some ⟨vf.pc, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
    rw [hf]
    cases vf
    simp_all
  cases o with
  | none =>
    obtain ⟨_, hrun⟩ := hX.thr g hg
    obtain ⟨_, _, hfire⟩ := hF
    have hlast := Run.end_last hrun hw (fires_none_ends hfire)
    have hflen : f < (X.tr g).length := PTX.len_of_get hf
    omega
  | some u =>
    exact ⟨f, vf.pc, ha, hFGet, j, by omega, d, w, u, hw, hstate,
      hbd.trans (hbl.trans hBlock), hsd, hsub', hF⟩

theorem store_before_publication {g a : Nat} {out : D} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (_ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, a) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g a = some (some (.wg0 out)))
    (hsite : out.site = .soReady) (site sub : Fin 4) :
    ∃ f ft, a = f + 1 ∧ X.get (g, f) = some ⟨ft, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      ∃ j < f, ∃ d w u, X.get (g, j) = some w ∧
        Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧
        d.block = out.block ∧ d.site = .pStore site ∧ d.sub = sub.val ∧
        (Wg0.code P L g).toMachine.Fired (some d) w (some u) :=
  actual_store_before_publication hX hs he hd hsite site sub

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ProbabilityRelease
