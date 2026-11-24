-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The raw release follows the dequantizer's proxy fence -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2RawRelease

open PTX PTX.Flow

private def previous : Wg2.Site → Wg2.Site → Prop
  | .ready, prev => prev = .fence
  | .free, prev => prev = .ready
  | _, _ => True

variable {P : Params}

private theorem role_previous {L : Launch} {g : Nat} {d d' : Wg2.D} {e : Event}
    (hn : Wg2.next P L g d e = some (some d')) : previous d'.site d.site := by
  cases hd : d.site <;> cases hk : e.kind <;>
    simp only [Wg2.next, Wg2.nextSite, hd, hk, Option.some.injEq, reduceCtorEq] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp only [previous, Wg2.afterScale, Wg2.afterRaw, Wg2.afterStore, Wg2.afterFree,
      Wg2.lenOrigNext, Wg2.lenExtraNext]
    repeat' first | split_ifs | split
    all_goals simp_all

private theorem prev_wg2 {L : Launch} {g : Nat} {e : Event} {q : Machine.ThreadD} {d : Wg2.D}
    (hn : Machine.next P L g q e = some (some (.wg2 d))) (hd : d.site = .ready ∨ d.site = .free) :
    ∃ prev : Wg2.D, q = .wg2 prev ∧ previous d.site prev.site := by
  cases q
  case prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        fin_cases w <;> split_ifs at hn <;> cases hn
        simp only [Wg2.init, Wg2.firstSite] at hd
        split_ifs at hd <;> cases hd <;> contradiction
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  case wg2 d0 =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i q hq
      cases hn
      exact ⟨d0, rfl, role_previous hq⟩
    · split_ifs at hn <;> cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    all_goals repeat' split at hn
    all_goals cases hn

private theorem trace_previous {L : Launch} {X : Execution} {g i : Nat} {d : Wg2.D} {e : Event}
    (he : X.get (g, i) = some e)
    (hSt : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hSite : d.site = .ready ∨ d.site = .free) :
    ∃ j f prev, i = j + 1 ∧ X.get (g, j) = some f ∧ previous d.site prev.site ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 prev)) := by
  cases i with
  | zero =>
    rw [Frame.stateAt_zero] at hSt
    cases hSt
  | succ j =>
    have hLt : j + 1 < (X.tr g).length := PTX.len_of_get he
    have hLt' : j < (X.tr g).length := by omega
    have hf : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hLt'
    obtain ⟨q, hQ⟩ := FollowedPrefix.state_at hSt (Nat.le_succ j)
    have step := Frame.stateAt_succ (C := Machine.code P L) hf
    rw [hSt, hQ] at step
    change some (some (.wg2 d)) = Machine.next P L g q (X.tr g)[j] at step
    obtain ⟨prev, rfl, hp⟩ := prev_wg2 step.symm hSite
    exact ⟨j, _, prev, rfl, hf, hp, hQ⟩

private theorem fired_fence {L : Launch} {g : Nat} {d : Wg2.D} {e : Event} {o : Option TState}
    (hd : d.site = .fence) (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e o) :
    e.kind = .fenceProxy (.async (some (.shared .cta))) none := by
  obtain ⟨t, _, hf⟩ := hf
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  have hp : d.site.pc = 3595 := by rw [hd]; rfl
  rw [hp, Flow.code_fenceProxy_5] at hf
  change Fires t.pc (eventTmpl Assumptions.all L g t
    (.fence (.proxy (.async (some (.shared .cta)))))) e o at hf
  rw [Wg2.event_fence] at hf
  exact congrArg Event.kind hf.1

/-- The dequant-ready arrival follows its shared async proxy fence immediately. -/
theorem fence_before_ready {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Wg2.D}
    {e : Event} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hSt : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) (hSite : d.site = .ready)
    :
    ∃ j, i = j + 1 ∧ X.IsProxyFence (g, j) (.async (some (.shared .cta))) none := by
  obtain ⟨j, f, fence, hindi, hf, hF, hFence⟩ := trace_previous he hSt (.inl hSite)
  have hSiteF : fence.site = .fence := by simpa [hSite, previous] using hF
  obtain ⟨_, hfire⟩ := RingEvents.fired_of_trace hX hs hf hFence
  have hk := fired_fence hSiteF hfire
  obtain ⟨site, kind⟩ := f
  exact ⟨j, hindi, site, by rw [hf]; cases hk; rfl⟩

/-- A raw-free release is two events after the shared async proxy fence of its path. -/
theorem fence_before_free {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Wg2.D}
    {e : Event} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hSt : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) (hSite : d.site = .free) :
    ∃ j f ready fence, i = j + 2 ∧ X.get (g, j) = some f ∧
      f.kind = .fenceProxy (.async (some (.shared .cta))) none ∧
      ready.site = .ready ∧ fence.site = .fence ∧
      Frame.stateAt (Machine.code P L) X g (j + 1) = some (some (.wg2 ready)) ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 fence)) := by
  obtain ⟨k, w, ready, hk, hw, hR, hReady⟩ := trace_previous he hSt (.inr hSite)
  have hSiteR : ready.site = .ready := by simpa [hSite, previous] using hR
  obtain ⟨j, f, fence, hj, hf, hF, hFence⟩ := trace_previous hw hReady (.inl hSiteR)
  have hSiteF : fence.site = .fence := by simpa [hSiteR, previous] using hF
  obtain ⟨_, hfire⟩ := RingEvents.fired_of_trace hX hs hf hFence
  exact ⟨j, f, ready, fence, by omega, hf, fired_fence hSiteF hfire,
    hSiteR, hSiteF, hj ▸ hReady, hFence⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2RawRelease
