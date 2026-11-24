-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingProgress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

public section

/-! # Actual successor sites of the CTA closing barrier -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.CtaClosingTrace

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def controlWarpgroup (L : Launch) (g : Nat) : Option Machine.ThreadD → Prop
  | some .head | some (.mma _) | some (.tma _) | some (.idle _) => wgOf L g = 1
  | _ => True

private theorem controlWarpgroup_next {d d' : Option Machine.ThreadD} {e : Event}
    (h : controlWarpgroup L g d)
    (hn : (Machine.machine P L g).next d e = some d') :
    controlWarpgroup L g d' := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn with hg
          · fin_cases w <;> cases hn <;> first | exact hg | trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> first | exact h | trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals first | exact h | trivial

private theorem controlWarpgroup_of_trace {i : Nat} {d : Machine.ThreadD}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some d)) :
    controlWarpgroup L g (some d) :=
  (hs.produces (hX.thr g hg)).prefix_induction (fun q _ => controlWarpgroup L g q)
    trivial (fun _ _ _ _ _ h _ hn => controlWarpgroup_next h hn) i (some d) hst

private theorem everyone_sub_zero {i : Nat} {e : Event} {d : Wg0.D}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .everyone) : d.sub = 0 := by
  obtain ⟨_, _, _, _, hinv, _, _⟩ := Frame.fired_site hs hX he hst
  have hd : Wg0.Inv P L g d := hinv
  simpa [hsite, Wg0.Site.elems] using hd.subLt

/-- The closing CTA arrival leads either to the return or to warp zero's deallocation. -/
theorem after_arrival {i tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some ⟨tag, .bar 12 none .sync⟩) :
    (∃ d, Frame.stateAt (Machine.code P L) X g (i + 1) = some (some d) ∧
      ClosingProgress.ReturnSite d ∧ warpOf L g ≠ 0) ∨
    (∃ d, Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 d)) ∧
      d.site = .exit ∧ warpOf L g = 0) := by
  obtain ⟨s, hst, hc, _, _⟩ := ScoreClosingGate.closing_at hpre hX hs ht he
  have hg := Frame.lt_of_get hX he
  have hgeo := RingRoleGeometry.of_trace hX hg (hs g hg).machine hst
  have hcontrol := controlWarpgroup_of_trace hX hg (hs g hg).machine hst
  rw [Frame.stateAt_succ he, hst, Option.bind_some]
  change (∃ d, Machine.next P L g s ⟨tag, .bar 12 none .sync⟩ = some (some d) ∧
      ClosingProgress.ReturnSite d ∧ warpOf L g ≠ 0) ∨
    (∃ d, Machine.next P L g s ⟨tag, .bar 12 none .sync⟩ = some (some (.wg0 d)) ∧
      d.site = .exit ∧ warpOf L g = 0)
  cases s
  case wg0 d =>
    change d.site = .everyone at hc
    have hsub := everyone_sub_zero hX hs he hst hc
    by_cases hw : warpOf L g = 0
    · exact .inr ⟨{ d with site := .exit, sub := 0 }, by
        simp [Machine.next, Wg0.next, Wg0.nextSite, hc, hw, hsub], rfl, hw⟩
    · exact .inl ⟨.done, by simp [Machine.next, Wg0.next, Wg0.nextSite, hc, hw], trivial, hw⟩
  case mma d =>
    change d.site = .outBar at hc
    have hw : warpOf L g ≠ 0 := by
      have hm : warpOf L g = 4 := hgeo
      omega
    exact .inl ⟨.mma { d with site := .exit }, by simp [Machine.next, Wg1Mma.next, hc], rfl, hw⟩
  case tma d =>
    change d.site = .barrier at hc
    have hw : warpOf L g ≠ 0 := by
      have hm : warpOf L g = 5 := hgeo
      omega
    exact .inl ⟨.tma { d with site := .exit }, by simp [Machine.next, Wg1Tma.next, hc], rfl, hw⟩
  case index d =>
    change d.site = .barrier at hc
    have hw : warpOf L g ≠ 0 := by
      have hm : warpOf L g = 7 := hgeo
      omega
    exact .inl ⟨.done, by simp [Machine.next, Wg1Index.next, Wg1Index.nextSite, hc], trivial, hw⟩
  case idle q =>
    change q = .sync at hc
    subst q
    have hw : warpOf L g ≠ 0 := by
      have hm : wgOf L g = 1 := hcontrol
      unfold wgOf warpOf at *
      omega
    exact .inl ⟨.idle .exit, by simp [Machine.next, Thread.next], rfl, hw⟩
  case wg2 d =>
    change d.site = .barrier at hc
    have hw : warpOf L g ≠ 0 := by
      have hm : wgOf L g = 2 := hgeo
      unfold wgOf warpOf at *
      omega
    exact .inl ⟨.done, by simp [Machine.next, Wg2.next, Wg2.nextSite, hc], trivial, hw⟩
  all_goals exact hc.elim

/-- A deallocation site visited by a real trace emits the resource request and leads to return. -/
theorem dealloc_at {i : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .exit) :
    (∃ tag, X.get (g, i) = some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩) ∧
    Frame.stateAt (Machine.code P L) X g (i + 1) = some (some .done) := by
  obtain ⟨_, ins, _, hat, _, hc, hf⟩ := Frame.fired_site hs hX he hd
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hsite] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
  change (Wg0.code P L g).AtD d _ at hat
  rw [Wg0.event_exit hpre hat hsite] at hf
  have heq := hf.1
  refine ⟨⟨_, he.trans (congrArg some heq)⟩, ?_⟩
  rw [Frame.stateAt_succ he, hd, heq]
  change Machine.next P L g (.wg0 d) _ = _
  simp [Machine.next, Wg0.next, Wg0.nextSite, hsite]
  rfl

/-- At a visited return site the actual event exits the thread. -/
theorem return_at {i : Nat} {d : Machine.ThreadD} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hsite : ClosingProgress.ReturnSite d) : ∃ tag, X.get (g, i) = some ⟨tag, .exit⟩ := by
  obtain ⟨_, _, _, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
  obtain rfl := Option.some.inj (hc.symm.trans (ClosingProgress.return_code hsite))
  exact ⟨_, he.trans (congrArg some hf.1)⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.CtaClosingTrace
