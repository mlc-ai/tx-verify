-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCausalInduction
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingArrivals
import Lemmas.Execution.EventFrameSource
import Lemmas.Flow.NotObject

@[expose] public section

/-! # Classifying observed ordinary releases in the causal tracking induction -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.EventFrame
open Protocol Protocol.IndexRing

private theorem run_returning_event {L : Launch} {g : Nat} {es : List Event}
    {e : Event} {t : TState} {outcome : Option TState}
    (hr : Run kernel Assumptions.all L g t es outcome) (he : e ∈ es) (hn : ¬ Ends e) :
    ∃ u v, EStep kernel Assumptions.all L g u e (some v) := by
  induction hr with
  | nil => simp at he
  | step _ h _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, _, h⟩
    · exact ih he
  | last _ h =>
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨_, _, h⟩ := h
    exact (hn (fires_none_ends h)).elim

private def localReleaseOp : Op → Bool
  | .mbarArrive _ _ _ _ cluster release scope _ => !cluster && release && decide (scope = .cta)
  | _ => true

set_option maxRecDepth 100000 in
private theorem all_arrivals_local_release :
    kernel.code.all (localReleaseOp ·.op) = true := by
  decide +kernel

/-- Every actual ordinary arrival in the frozen instruction trace releases its own CTA's object.
Only the raw event and the decoded release and address qualifiers enter. -/
theorem actual_arrive_fields {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat}
    {e : Event} {m : Loc} {tx count : Nat} {release : Bool} {scope : MbarScope}
    (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get (g, i) = some e)
    (hk : e.kind = .arrive m tx count release scope) :
    m.space = .shared ∧ m.cta = ctaOf L g ∧ release = true ∧ scope = .cta := by
  have hMem : e ∈ X.tr g := List.mem_of_getElem? he
  obtain ⟨_, hr⟩ := hX.thr g (Frame.lt_of_get hX he)
  obtain ⟨u, _, hu⟩ := run_returning_event hr hMem (by
    rw [Ends, hk]
    simp)
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source hu
  have hRelease := List.all_eq_true.mp all_arrivals_local_release ins (List.mem_of_getElem? hc)
  by_cases ha : ∃ b o x n l r s d, ins.op = .mbarArrive b o x n l r s d
  · obtain ⟨b, o, x, n, l, r, s, d, hop⟩ := ha
    rw [hop] at hf hRelease
    have hQualifiers : (l = false ∧ r = true) ∧ s = .cta := by
      simpa only [localReleaseOp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        using hRelease
    obtain ⟨⟨hl, hrel⟩, hscope⟩ := hQualifiers
    rw [hl, hrel, hscope] at hf
    have hw : Assumptions.all.any (·.clusterScopeMbar u.pc) = false := rfl
    simp only [eventTmpl, tmaTmpl, widenMbarScope, hw, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure] at hf
    cases hm : mbarLoc L g u b o with
    | error f => simp only [hm, ofExec, Fires] at hf; cases hf.2
    | ok mm =>
      rw [hm] at hf
      cases hx : readBits L g u 32 x with
      | error f => simp only [hx, ofExec, Fires] at hf; cases hf.2
      | ok xx =>
        rw [hx] at hf
        cases hn : readBits L g u 32 n with
        | error f => simp only [hn, ofExec, Fires] at hf; cases hf.2
        | ok nn =>
          simp only [hn, ofExec, Fires] at hf
          have hEq := Kind.arrive.inj (hk.symm.trans (congrArg Event.kind hf.1))
          obtain ⟨rfl, _, _, hR, hS⟩ := hEq
          exact ⟨(mbarLoc_local hm).1, (mbarLoc_local hm).2, hR, hS⟩
  · have hNone := eventTmpl_notArrive (A := Assumptions.all) (L := L) (g := g)
      (t := u) (fun b o x n l r s d h => ha ⟨b, o, x, n, l, r, s, d, h⟩)
    exact (fires_notArrive hNone hf m tx count release scope hk).elim

/-- An ordinary update of a ready object observed by the actual coordinate acquire is a real
index publication, using only the absence of causal predecessor dismissals. -/
theorem observed_ready_source {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {h j g i q : Nat} {e f : Event} {slot : Fin 4} {tx count : Nat}
    {release : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ w < L.threads, (Machine.code P L w).Sound)
    (he : X.get (g, i) = some e) (hq : q < i) (hf : X.get (h, j) = some f)
    (hKind : f.kind = .arrive (ready L (ctaOf L g) slot) tx count release scope)
    (hObserved : WaitObserves X (.thread (h, j)) (g, q) (ready L (ctaOf L g) slot) true .cta)
    (hPrior : ∀ w, baseCausality L X w (g, i) → ¬ Dismisses P L X w) :
    AtIndex P L X (ctaOf L g) slot h j (fun s => ∃ extra, s = .ready extra) ∧
      tx = 0 ∧ count = 1 ∧ release = true ∧ scope = .cta := by
  obtain ⟨_, hCta, rfl, rfl⟩ := actual_arrive_fields hX hf hKind
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX hf
  have hm : SameCta L h g := ⟨hh, hg, hCta.symm⟩
  have hb : MbarRelease X (h, j) (ready L (ctaOf L g) slot) .cta := by
    refine ⟨tx, count, f.pc, ?_⟩
    rw [hf, ← hKind]
  have hst := observed_release_predecessor he hq hb hObserved (ScopesMeet.of_sameCta hm) hPrior
  exact publish_source_at_tracked_event hpre hX (hs h hh).machine hst hf hKind

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
