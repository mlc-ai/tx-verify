-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWalkCheckpoint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section

/-- Split an actual loader walk at an audited cut, retaining its exact prefix and tail.
An observed returning event at or after the cut forces the walk to reach it. -/
theorem loaderObservedCut {l : Launch} {g scopeLower lower cut stop : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {F : List (Nat × Value)} {e : Event}
    (hScope : scopeLower ≤ lower) (hLo : 174 ≤ lower) (hHi : cut ≤ 1901) (hCut : cut < stop)
    (hCode : ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut (stop - 1) (F.map Prod.fst) ins.op) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) (hStart : lower ≤ s.pc ∧ s.pc ≤ cut)
    (hs : RingShape s) (hF : Holds s.regs F)
    (hSeen : e ∈ loaderSliceEvents scopeLower stop vs) (hEvent : cut ≤ e.pc)
    (hReturns : ¬ Ends e) :
    ∃ t pre tail front post, es = pre ++ tail ∧ vs = front ++ post ∧
      (∀ v ∈ front, lower ≤ v.pc ∧ v.pc < cut) ∧
      t.pc = cut ∧ RingShape t ∧ Holds t.regs F ∧
      Walk kernel Assumptions.all l g s pre front ∧
      Walk kernel Assumptions.all l g t tail post ∧ e ∈ loaderSliceEvents scopeLower stop post := by
  have step {s u : TState} {ev : Option Event} {tail : List Event} {post : List Visit}
      (hw : WStep kernel Assumptions.all l g s ev u)
      (hTail : Walk kernel Assumptions.all l g u tail post)
      (hStart : lower ≤ s.pc ∧ s.pc ≤ cut) (hs : RingShape s) (hF : Holds s.regs F)
      (hSeen : e ∈ loaderSliceEvents scopeLower stop (visit kernel l g s ev :: post))
      (ih : lower ≤ u.pc ∧ u.pc ≤ cut → RingShape u → Holds u.regs F →
        e ∈ loaderSliceEvents scopeLower stop post →
        ∃ t pre rest front vs, tail = pre ++ rest ∧ post = front ++ vs ∧
          (∀ v ∈ front, lower ≤ v.pc ∧ v.pc < cut) ∧
          t.pc = cut ∧ RingShape t ∧ Holds t.regs F ∧
          Walk kernel Assumptions.all l g u pre front ∧
          Walk kernel Assumptions.all l g t rest vs ∧ e ∈ loaderSliceEvents scopeLower stop vs) :
      ∃ t pre rest front vs, ev.toList ++ tail = pre ++ rest ∧
        visit kernel l g s ev :: post = front ++ vs ∧
        (∀ v ∈ front, lower ≤ v.pc ∧ v.pc < cut) ∧
        t.pc = cut ∧ RingShape t ∧ Holds t.regs F ∧
        Walk kernel Assumptions.all l g s pre front ∧
        Walk kernel Assumptions.all l g t rest vs ∧ e ∈ loaderSliceEvents scopeLower stop vs := by
    have prepend {evs visits} (h : Walk kernel Assumptions.all l g u evs visits) :
        Walk kernel Assumptions.all l g s (ev.toList ++ evs) (visit kernel l g s ev :: visits) := by
      rcases hw with ⟨rfl, ht⟩ | ⟨a, rfl, he⟩
      · exact .tau ht h
      · exact .ev he h
    by_cases hHere : s.pc = cut
    · exact ⟨s, [], _, [], _, rfl, rfl, by simp, hHere, hs, hF, .stop s, prepend hTail, hSeen⟩
    have hLt : s.pc < cut := by omega
    have hStop : s.pc < stop := hLt.trans hCut
    have hScopeLo : scopeLower ≤ s.pc := hScope.trans hStart.1
    have hNext : e ∈ loaderSliceEvents scopeLower stop post := by
      rcases hw with ⟨rfl, _⟩ | ⟨a, rfl, he⟩
      · simpa [loaderSliceEvents, visit, hScopeLo, hStop] using hSeen
      · have hNe : e ≠ a := by
          intro h
          have := estep_source_pc he
          subst a
          omega
        simpa [loaderSliceEvents, visit, hScopeLo, hStop, hNe] using hSeen
    obtain ⟨hLow, hUp | hOut, hShape, hNew⟩ := pipelineCutStep hLo hHi
      ⟨hStart.1, hLt⟩ hCode hw hs hF
    · obtain ⟨t, pre, rest, front, vs, hEs, hVs, hScope, ht, hT, hf, hPre, hW, hSaw⟩ :=
        ih ⟨hLow, hUp⟩ hShape hNew hNext
      refine ⟨t, ev.toList ++ pre, rest, visit kernel l g s ev :: front, vs,
        by simp [hEs, List.append_assoc], by simp [hVs], ?_, ht, hT, hf, prepend hPre, hW,
        hSaw⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hm
      · simpa only [visit_pc] using And.intro hStart.1 hLt
      · exact hScope v hm
    · have hu : ¬u.pc < stop := by omega
      cases post with
      | nil => simp [loaderSliceEvents] at hNext
      | cons first rest =>
        have hp := hTail.zero_pc rfl
        simp [loaderSliceEvents, hp, hu] at hNext
  induction hw with
  | stop => simp [loaderSliceEvents] at hSeen
  | tau ht hTail ih =>
    exact step (.inl ⟨rfl, ht⟩) hTail hStart hs hF hSeen ih
  | ev he hTail ih =>
    exact step (.inr ⟨_, rfl, he⟩) hTail hStart hs hF hSeen ih
  | @last t a he =>
    have hInside : scopeLower ≤ t.pc ∧ t.pc < stop :=
      ⟨hScope.trans hStart.1, hStart.2.trans_lt hCut⟩
    have hEq : e = a := by simpa [loaderSliceEvents, visit, hInside.1, hInside.2] using hSeen
    obtain ⟨_, _, hFire⟩ := he
    exact (hReturns (hEq.symm ▸ fires_none_ends hFire)).elim

end
end PTX.Kernels.TmlFa4Fwd.Loader
