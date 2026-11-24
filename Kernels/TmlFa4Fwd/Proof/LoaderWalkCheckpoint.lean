-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
public import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- Events while the actual walk remains in the indicated half-open PC interval. -/
def loaderSliceEvents (lower stop : Nat) (visits : List Visit) : List Event :=
  (visits.takeWhile (fun v => lower ≤ v.pc && v.pc < stop)).filterMap Visit.ev

variable {l : Launch}

private theorem faultHasNoCopy {g lower stop : Nat} {s : TState} {es : List Event} {vs : List Visit}
    {e : Event} {sp : AsyncCopy.Spec} (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : e ∈ loaderSliceEvents lower stop vs) (hKind : e.kind = .copy sp) :
    s.fault = none := by
  cases hf : s.fault
  · rfl
  cases hw with
  | stop => simp [loaderSliceEvents] at hSeen
  | tau ht _ => simp [Tau, out, hf] at ht
  | ev he _ =>
    obtain ⟨t, ho, hFire⟩ := he
    simp only [out, hf, Out.ev.injEq] at ho
    subst t
    cases hFire.2
  | last he =>
    obtain ⟨_, _, hFire⟩ := he
    have hEnd := fires_none_ends hFire
    by_cases hk : lower ≤ s.pc ∧ s.pc < stop
    · obtain rfl : e = _ := by simpa [loaderSliceEvents, visit, hk.1, hk.2] using hSeen
      simp [Ends, hKind] at hEnd
    · simp [loaderSliceEvents, visit, hk] at hSeen

/-- A copy observed inside an audited control-flow slice must pass its local
checkpoint with the requested register frame. The returned walk retains the issue. -/
theorem loaderCopyThroughCheckpoint {g scopeLower lower cut stop : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {F : List (Nat × Value)} {e : Event} {sp : AsyncCopy.Spec}
    (hScopeLower : scopeLower ≤ lower) (hLower : 174 ≤ lower) (hCut : cut ≤ 1901)
    (hBefore : cut < stop) (hLocal : ∃ ins, kernel.code[cut]? = some ins ∧ ins.op.isLocal = true)
    (hCode : ((kernel.code.drop lower).take (cut - lower)).all
      (fun ins => loaderPipelineCutOp lower cut (stop - 1) (F.map Prod.fst) ins.op) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) (hp : lower ≤ s.pc ∧ s.pc ≤ cut)
    (hs : RingShape s) (hF : Holds s.regs F) (hSeen : e ∈ loaderSliceEvents scopeLower stop vs)
    (hPC : cut ≤ e.pc) (hKind : e.kind = .copy sp) :
    ∃ t es' vs', At t cut F ∧ Walk kernel Assumptions.all l g t es' vs' ∧
      vs' <:+ vs ∧ e ∈ loaderSliceEvents scopeLower stop vs' := by
  have step {t u : TState} {ev : Option Event} {tailEs : List Event} {tailVs : List Visit}
      (hW : Walk kernel Assumptions.all l g t (ev.toList ++ tailEs)
        (visit kernel l g t ev :: tailVs))
      (hwTail : Walk kernel Assumptions.all l g u tailEs tailVs)
      (hStep : WStep kernel Assumptions.all l g t ev u)
      (hHere : lower ≤ t.pc ∧ t.pc ≤ cut) (ht : RingShape t) (hReg : Holds t.regs F)
      (hIssue : e ∈ loaderSliceEvents scopeLower stop (visit kernel l g t ev :: tailVs))
      (ih : (lower ≤ u.pc ∧ u.pc ≤ cut) → RingShape u → Holds u.regs F →
        e ∈ loaderSliceEvents scopeLower stop tailVs →
          ∃ v moreEs moreVs, At v cut F ∧ Walk kernel Assumptions.all l g v moreEs moreVs ∧
            moreVs <:+ tailVs ∧ e ∈ loaderSliceEvents scopeLower stop moreVs) :
      ∃ q restEs restVs, At q cut F ∧ Walk kernel Assumptions.all l g q restEs restVs ∧
        restVs <:+ (visit kernel l g t ev :: tailVs) ∧
        e ∈ loaderSliceEvents scopeLower stop restVs := by
    by_cases hc : t.pc = cut
    · exact ⟨t, _, _, pipelineAtCut hc ht hReg (faultHasNoCopy hW hIssue hKind) hLocal,
        hW, List.suffix_rfl, hIssue⟩
    have before : t.pc < cut := by omega
    have inScope : t.pc < stop := before.trans hBefore
    have hScope : scopeLower ≤ t.pc := hScopeLower.trans hHere.1
    have hTail : e ∈ loaderSliceEvents scopeLower stop tailVs := by
      rcases hStep with ⟨rfl, _⟩ | ⟨ev', rfl, he⟩
      · simpa [loaderSliceEvents, visit, hScope, inScope] using hIssue
      · have hPc := estep_source_pc he
        simp [loaderSliceEvents, visit, hScope, inScope] at hIssue
        rcases hIssue with rfl | hMem
        · omega
        · exact List.mem_filterMap.mpr hMem
    obtain ⟨hLo, hL | hR, hShape, hRegs⟩ :=
      pipelineCutStep hLower hCut ⟨hHere.1, before⟩ hCode hStep ht hReg
    · obtain ⟨s', es', vs', hAt, hw', hSuf, hMem⟩ := ih ⟨hLo, hL⟩ hShape hRegs hTail
      exact ⟨s', es', vs', hAt, hw', hSuf.trans ⟨[_], rfl⟩, hMem⟩
    · have hBeyond : ¬ u.pc < stop := by omega
      cases tailVs with
      | nil => simp [loaderSliceEvents] at hTail
      | cons first rest =>
        have hp := hwTail.zero_pc rfl
        simp [loaderSliceEvents, hp, hBeyond] at hTail
  induction hw with
  | stop => simp [loaderSliceEvents] at hSeen
  | tau ht hw ih => exact step (.tau ht hw) hw (.inl ⟨rfl, ht⟩) hp hs hF hSeen ih
  | ev he hw ih => exact step (.ev he hw) hw (.inr ⟨_, rfl, he⟩) hp hs hF hSeen ih
  | @last t e' he =>
    obtain ⟨_, _, hFire⟩ := he
    have hEnd := fires_none_ends hFire
    by_cases hScope : scopeLower ≤ t.pc ∧ t.pc < stop
    · have heq : e = e' := by simpa [loaderSliceEvents, visit, hScope.1, hScope.2] using hSeen
      simp [Ends, ← heq, hKind] at hEnd
    · simp [loaderSliceEvents, visit, hScope] at hSeen

/-- A recorded event after a local segment survives removal of the segment from
the actual walk. A stopped prefix within the local segment cannot record the event. -/
theorem loaderEventAfterLocal {g lower stop n : Nat} {s u : TState} {es : List Event}
    {vs : List Visit} {e : Event} (hr : run kernel Assumptions.all l g n s = some u)
    (hw : Walk kernel Assumptions.all l g s es vs) (hSeen : e ∈ loaderSliceEvents lower stop vs) :
    ∃ tail, Walk kernel Assumptions.all l g u es tail ∧
      tail <:+ vs ∧ e ∈ loaderSliceEvents lower stop tail := by
  induction n generalizing s es vs with
  | zero =>
    obtain rfl := Option.some.inj hr
    exact ⟨vs, hw, List.suffix_rfl, hSeen⟩
  | succ n ih =>
    simp only [run] at hr
    cases hn : tauStep kernel Assumptions.all l g s with
    | none => simp [hn] at hr
    | some t =>
      rw [hn, Option.bind_some] at hr
      have ht := tauStep_iff.mp hn
      cases hw with
      | stop => simp [loaderSliceEvents] at hSeen
      | @tau _ v es visits hSame hw =>
        obtain rfl : t = v := Option.some.inj (hn.symm.trans (tauStep_iff.mpr hSame))
        have hRest : e ∈ loaderSliceEvents lower stop visits := by
          by_cases hp : lower ≤ s.pc ∧ s.pc < stop
          · simpa [loaderSliceEvents, visit, hp.1, hp.2] using hSeen
          · simp [loaderSliceEvents, visit, hp] at hSeen
        obtain ⟨rest, hTail, hSuf, hSaw⟩ := ih hr hw hRest
        exact ⟨rest, hTail, hSuf.trans ⟨[_], rfl⟩, hSaw⟩
      | ev he _ =>
        obtain ⟨_, ho, _⟩ := he
        unfold Tau at ht
        rw [ho] at ht
        cases ht
      | last he =>
        obtain ⟨_, ho, _⟩ := he
        unfold Tau at ht
        rw [ho] at ht
        cases ht

private theorem loaderStraightPc {op : Op} {pc : Nat}
    (hSeq : Epilogue.schedulerFallsThrough op = true) :
    nextPc op pc = pc + 1 ∧ ∀ target, ¬ BrxTarget op target := by
  cases op <;> simp_all [nextPc, BrxTarget, Epilogue.schedulerFallsThrough]

/-- A local section that is straight-line and has no writes to the selected
registers preserves their values in the actual loader profile. -/
theorem loaderSegmentFrame {g lower stop n : Nat} {s u : TState} {regs : List Nat}
    (hLower : 174 ≤ lower) (hUpper : stop ≤ 1901)
    (hCode : ((kernel.code.drop lower).take (stop - lower)).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op &&
        regs.all fun r => !(loaderRingWrites ins.op).contains r) = true)
    (hRun : run kernel Assumptions.all l g n s = some u) (hLo : lower ≤ s.pc)
    (hHi : s.pc + n ≤ stop) :
    u.pc = s.pc + n ∧ ∀ r ∈ regs, u.regs r = s.regs r := by
  induction n generalizing s with
  | zero =>
    obtain rfl := Option.some.inj hRun
    exact ⟨by simp, fun _ _ => rfl⟩
  | succ n ih =>
    simp only [run] at hRun
    cases hNext : tauStep kernel Assumptions.all l g s with
    | none => simp [hNext] at hRun
    | some t =>
      rw [hNext, Option.bind_some] at hRun
      have hTau := tauStep_iff.mp hNext
      have hCore : Tau kernel [] l g s t := by
        unfold Tau at hTau ⊢
        rwa [← loaderOutCore (by omega) (by omega)]
      obtain ⟨ins, hc⟩ := tau_core_has_code hCore
      have hGet : ((kernel.code.drop lower).take (stop - lower))[s.pc - lower]? = some ins := by
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
        exact hc
      obtain ⟨hFalls, hRegs⟩ := Bool.and_eq_true_iff.mp
        (List.all_eq_true.mp hCode _ (List.mem_of_getElem? hGet))
      have hStepPc : t.pc = s.pc + 1 := by
        rcases tau_core_frame hc hCore with rfl | hf
        · rfl
        · have h := loaderStraightPc (pc := s.pc) hFalls
          exact (hf.pc.resolve_right (h.2 _)).trans h.1
      have hStepReg (r : Nat) (hr : r ∈ regs) : t.regs r = s.regs r := by
        apply loaderPipelineStepRegs (by omega) (by omega) _ (.inl ⟨rfl, hTau⟩)
        intro instr hInstr
        obtain rfl := Option.some.inj (hc.symm.trans hInstr)
        simpa using List.all_eq_true.mp hRegs r hr
      obtain ⟨hp, hPres⟩ := ih hRun (by omega) (by omega)
      exact ⟨by omega, fun r hr => (hPres r hr).trans (hStepReg r hr)⟩

/-- Recover the source state of an observed nonterminal event in a slice that preserves the
specified registers. The certificate validates every decoded transition. -/
theorem loaderEventWithRegisters {g scopeLower lower stop : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {F : List (Nat × Value)} {e : Event} (hScope : scopeLower ≤ lower)
    (hLower : 174 ≤ lower) (hLimit : stop ≤ 1901)
    (hCode : ((kernel.code.drop lower).take (stop - lower)).all
      (fun ins => loaderPipelineCutOp lower stop (stop - 1) (F.map Prod.fst) ins.op) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) (hp : lower ≤ s.pc) (hs : RingShape s)
    (hF : Holds s.regs F) (hSeen : e ∈ loaderSliceEvents scopeLower stop vs) (hKind : ¬ Ends e) :
    ∃ t u, t.pc = e.pc ∧ Holds t.regs F ∧ EStep kernel Assumptions.all l g t e (some u) := by
  have step {t u : TState} {ev : Option Event} {tailVs : List Visit}
      (hStep : WStep kernel Assumptions.all l g t ev u)
      (hPc : lower ≤ t.pc) (hShape : RingShape t) (hReg : Holds t.regs F)
      (hIssue : e ∈ loaderSliceEvents scopeLower stop (visit kernel l g t ev :: tailVs))
      (ih : lower ≤ u.pc → RingShape u → Holds u.regs F →
        e ∈ loaderSliceEvents scopeLower stop tailVs →
          ∃ v w, v.pc = e.pc ∧ Holds v.regs F ∧ EStep kernel Assumptions.all l g v e (some w)) :
      ∃ v w, v.pc = e.pc ∧ Holds v.regs F ∧ EStep kernel Assumptions.all l g v e (some w) := by
    have hLo := hScope.trans hPc
    have hHi : t.pc < stop := by
      by_contra hBad
      simp [loaderSliceEvents, visit, hLo, hBad] at hIssue
    obtain ⟨hNextLo, _, hNextShape, hNextReg⟩ :=
      pipelineCutStep hLower hLimit ⟨hPc, hHi⟩ hCode hStep hShape hReg
    rcases hStep with ⟨rfl, _⟩ | ⟨ev', rfl, he⟩
    · exact ih hNextLo hNextShape hNextReg
        (by simpa [loaderSliceEvents, visit, hLo, hHi] using hIssue)
    · simp [loaderSliceEvents, visit, hLo, hHi] at hIssue
      rcases hIssue with rfl | hTail
      · exact ⟨t, u, (estep_source_pc he).symm, hReg, he⟩
      · exact ih hNextLo hNextShape hNextReg (List.mem_filterMap.mpr hTail)
  induction hw with
  | stop => simp [loaderSliceEvents] at hSeen
  | tau ht hw ih => exact step (.inl ⟨rfl, ht⟩) hp hs hF hSeen ih
  | ev he hw ih => exact step (.inr ⟨_, rfl, he⟩) hp hs hF hSeen ih
  | @last t ev he =>
    obtain ⟨_, _, hFire⟩ := he
    have hEnd := fires_none_ends hFire
    by_cases hRoom : t.pc < stop
    · have heq : e = ev := by
        simpa [loaderSliceEvents, visit, hScope.trans hp, hRoom] using hSeen
      exact (hKind (heq ▸ hEnd)).elim
    · simp [loaderSliceEvents, visit, hRoom] at hSeen

/-- Recover the source state of an observed copy while retaining the register frame. -/
theorem loaderCopyWithRegisters {g scopeLower lower stop : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {F : List (Nat × Value)} {e : Event} {sp : AsyncCopy.Spec}
    (hScope : scopeLower ≤ lower) (hLower : 174 ≤ lower) (hLimit : stop ≤ 1901)
    (hCode : ((kernel.code.drop lower).take (stop - lower)).all
      (fun ins => loaderPipelineCutOp lower stop (stop - 1) (F.map Prod.fst) ins.op) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) (hp : lower ≤ s.pc) (hs : RingShape s)
    (hF : Holds s.regs F) (hSeen : e ∈ loaderSliceEvents scopeLower stop vs)
    (hKind : e.kind = .copy sp) :
    ∃ t u, t.pc = e.pc ∧ Holds t.regs F ∧ EStep kernel Assumptions.all l g t e (some u) :=
  loaderEventWithRegisters hScope hLower hLimit hCode hw hp hs hF hSeen (by simp [Ends, hKind])

end
end PTX.Kernels.TmlFa4Fwd.Loader
