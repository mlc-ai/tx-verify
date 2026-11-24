-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLoopRank
public import Kernels.TmlFa4Fwd.Proof.MmaScanBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private def scanRank (site : ScanSite) (batch group pc : Nat) : Nat :=
  64 * (batch - group + 1) + (if pc = site.head then 0 else site.compare + 3 - pc)

private theorem groupScanRegs {scan : GroupScan} {first batch cta : Nat} :
    ∀ pair ∈ groupScanFacts scan first batch cta, pair.1 ∈ scanFrame (scanSite scan) := by
  simp only [scanFrame, groupScanFacts, List.mem_cons, List.not_mem_nil, or_false]
  rintro pair (rfl | rfl | rfl | rfl) <;> simp

private theorem scanHeadBeforeBody (scan : GroupScan) :
    (scanSite scan).head < (scanSite scan).head + 5 := by omega

private theorem scanBodyWidth (scan : GroupScan) :
    (scanSite scan).compare + 3 - ((scanSite scan).head + 5) = 49 := by
  cases scan <;> rfl

private theorem scanHeadCode (scan : GroupScan) :
    ∃ pred, kernel.code[(scanSite scan).compare + 2]? =
      some ⟨some (pred, false), .bra (scanSite scan).head false⟩ := by
  cases scan
  · exact ⟨_, Flow.code_2041⟩
  · exact ⟨_, Flow.code_2749⟩
  · exact ⟨_, Flow.code_2877⟩
  · exact ⟨_, Flow.code_3085⟩
  · exact ⟨_, Flow.code_3211⟩
  · exact ⟨_, Flow.code_7719⟩
  · exact ⟨_, Flow.code_7863⟩
  · exact ⟨_, Flow.code_9186⟩
  · exact ⟨_, Flow.code_287⟩
  · exact ⟨_, Flow.code_1847⟩

theorem scanEndTau (scan : GroupScan) {l : Launch} {g : Nat} {s u : TState}
    (hs : s.pc = (scanSite scan).compare + 2) (hSub : s.sub = 0) (hAcc : s.acc = [])
    (h : Tau kernel Assumptions.all l g s u) :
    (u.pc = (scanSite scan).head ∨ u.pc = (scanSite scan).compare + 3) ∧
      u.sub = s.sub ∧ u.acc = s.acc ∧ u.fault = s.fault ∧ u.regs = s.regs := by
  have h' : Tau kernel [] l g s u := by
    unfold Tau at h ⊢
    have hWidth := scanBodyWidth scan
    rwa [← groupScanOut scan (by omega) (by omega)]
  obtain ⟨pred, hc⟩ := scanHeadCode scan
  rw [← hs] at hc
  rcases tau_core_frame hc h' with rfl | hFrame
  · exact ⟨.inr (by simp [skip, hs, Nat.add_assoc]), hSub.symm, hAcc.symm, rfl, rfl⟩
  · exact ⟨.inl (hFrame.pc.resolve_right id), hFrame.sub, hFrame.acc, hFrame.fault,
      funext fun r => hFrame.regs r (by simp [writesRegs])⟩

private theorem pastScanCount (scan : GroupScan) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : s.pc = (scanSite scan).compare + 3) :
    countedUntil ((scanSite scan).compare + 3) vs = 0 := by
  cases hw <;> simp [countedUntil, visit_pc, hPc]

private theorem scanCountLe (scan : GroupScan) {l : Launch} {g batch cta : Nat}
    (hBatch : batch + 31 < 2 ^ 31) (hCta : cta + 1 < 2 ^ 31) :
    ∀ fuel first {s : TState} {es : List Event} {vs : List Visit},
      vs.length = fuel → first ≤ batch →
      (s.pc = (scanSite scan).head ∨
        (scanSite scan).head + 5 ≤ s.pc ∧ s.pc ≤ (scanSite scan).compare + 2) →
      At s s.pc (groupScanFacts scan first batch cta) →
      Walk kernel Assumptions.all l g s es vs →
      countedUntil ((scanSite scan).compare + 3) vs ≤
        scanRank (scanSite scan) batch first s.pc := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro first s es vs hLen hFirst hRange ht hw
    let site := scanSite scan
    let cutoff := site.compare + 3
    have hHead : site.head < site.head + 5 := scanHeadBeforeBody scan
    have hFlip : site.head + 5 < cutoff := by cases scan <;> decide
    rcases hRange with hP | ⟨hLo, hHi⟩
    · have hInit : At s site.head (groupScanFacts scan first batch cta) := by
        simpa only [hP] using ht
      have hB : batch < 2 ^ 31 := by omega
      have hNext : first + 31 < 2 ^ 31 := by omega
      obtain ⟨u, hu, hU⟩ := advanceGroupScanFramed (l := l) (g := g) scan hNext hB hInit
      have hPath := advanceWalkLocals hu hw
      rcases hPath with he | ⟨post, hPost, hCut, hWalk⟩
      · subst es
        simp [zeroCountNoEvents hw]
      · by_cases hClip : batch ≤ first + 31
        · rw [ite_eq_left hClip] at hU
          have hCore : At u site.compare [(site.work, b32 (cta + 1)), (site.cta, b32 cta)] :=
            hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.2.2.2.1, trivial⟩
          obtain ⟨v, hv, hV⟩ := exhaustedGroupScan (l := l) (g := g) scan hCta hCore
          rcases advanceWalkLocals hv hWalk with hEmpty | ⟨tail, _, hLater, hTail⟩
          · subst es
            simp [zeroCountNoEvents hw]
          · have hZero := pastScanCount scan hTail hV.1
            have hCount := (hCut cutoff).trans (hLater cutoff)
            change _ ≤ countedUntil ((scanSite scan).compare + 3) tail at hCount
            rw [hZero] at hCount
            exact hCount.trans (Nat.zero_le _)
        · rw [ite_eq_right hClip, Nat.min_eq_left (by omega : first + 31 ≤ batch)] at hU
          have hAt : At u u.pc (groupScanFacts scan (first + 31) batch cta) := by
            exact ⟨rfl, hU.2.1, hU.2.2.1, hU.2.2.2.1, hU.2.2.2.2.2⟩
          have hPc := hU.1
          have hNextRange : (scanSite scan).head + 5 ≤ u.pc ∧
              u.pc ≤ (scanSite scan).compare + 2 := by
            have hLen' := scanBodyWidth scan
            change (scanSite scan).head + 5 ≤ u.pc ∧ u.pc ≤ (scanSite scan).compare + 2
            change u.pc = (scanSite scan).head + 5 at hPc
            omega
          have hc := ih post.length (by omega) (first + 31) rfl (by omega)
            (.inr hNextRange) hAt hWalk
          apply (hCut cutoff).trans (hc.trans ?_)
          have hLen' := scanBodyWidth scan
          change u.pc = (scanSite scan).head + 5 at hPc
          change (scanSite scan).head < (scanSite scan).head + 5 at hHead
          simp only [scanRank, hPc, ite_eq_right hHead.ne.symm, ↓reduceIte, hP,
            hLen', Nat.add_zero]
          omega
    · have hRange' : site.head + 5 ≤ s.pc ∧ s.pc ≤ site.compare + 2 := ⟨hLo, hHi⟩
      clear hLo hHi
      obtain ⟨hLo, hHi⟩ := hRange'
      have hsCut : s.pc < cutoff := by omega
      have hsNotHead : s.pc ≠ site.head := by omega
      change countedUntil cutoff vs ≤ scanRank site batch first s.pc
      cases hw with
      | stop => simp [countedUntil]
      | @tau s u es vs hTau hw =>
        have hSmaller : vs.length < fuel := by simp only [List.length_cons] at hLen; omega
        by_cases hEnd : s.pc = site.compare + 2
        · obtain ⟨hPc | hPc, hSub, hAcc, hFault, hRegs⟩ :=
            scanEndTau scan hEnd ht.2.1 ht.2.2.1 hTau
          · have hU : At u u.pc (groupScanFacts scan first batch cta) := by
              exact ⟨rfl, hSub.trans ht.2.1, hAcc.trans ht.2.2.1, hFault.trans ht.2.2.2.1,
                hRegs.symm ▸ ht.2.2.2.2⟩
            have h := ih vs.length hSmaller first rfl hFirst (.inl hPc) hU hw
            have hBody : countedUntil cutoff vs ≤ scanRank site batch first s.pc := by
              refine h.trans ?_
              simp [scanRank, hPc]
            simpa [countedUntil, hsCut, visit_pc, visit_ev, List.filterMap_cons] using hBody
          · have hZero := pastScanCount scan hw hPc
            have hBody : countedUntil cutoff vs ≤ scanRank site batch first s.pc := by
              change countedUntil ((scanSite scan).compare + 3) vs ≤ _
              simp [hZero]
            simpa [countedUntil, hsCut, visit_pc, visit_ev, List.filterMap_cons] using hBody
        · have hLt : s.pc < site.compare + 2 := by omega
          obtain ⟨hAdv, hCap, hSub, hAcc, hFault, hRegs⟩ :=
            scanBodyTau scan hLo hLt ht.2.1 ht.2.2.1 hTau
          have hU : At u u.pc (groupScanFacts scan first batch cta) := by
            refine ⟨rfl, hSub.trans ht.2.1, hAcc.trans ht.2.2.1, hFault.trans ht.2.2.2.1, ?_⟩
            exact Epilogue.holdsSchedulerFrame ht.2.2.2.2 hRegs groupScanRegs
          have hUlo : site.head + 5 ≤ u.pc := by omega
          have hUn : u.pc ≠ site.head := by omega
          have hCount := ih vs.length hSmaller first rfl hFirst (.inr ⟨hUlo, hCap⟩) hU hw
          have hMon : scanRank site batch first u.pc ≤ scanRank site batch first s.pc := by
            simp only [scanRank, ite_eq_right hsNotHead, ite_eq_right hUn]
            omega
          have hBody : countedUntil cutoff vs ≤ scanRank site batch first s.pc := hCount.trans hMon
          simpa [countedUntil, hsCut, visit_pc, visit_ev, List.filterMap_cons] using hBody
      | @ev s u e es vs he hw =>
        have hSmaller : vs.length < fuel := by simp only [List.length_cons] at hLen; omega
        have hLt : s.pc < site.compare + 2 := by
          by_contra! hStop
          have hPC : s.pc = site.compare + 2 := by omega
          obtain ⟨pred, hc⟩ := scanHeadCode scan
          obtain ⟨i, hi, hLocal, _⟩ := estep_event_source he
          change s.pc = (scanSite scan).compare + 2 at hPC
          rw [← hPC, hi] at hc
          cases hc
          cases hLocal
        obtain ⟨hAdvance | hFault, hSub, hAcc, hRegs⟩ :=
          scanBodyEvent scan hLo hLt ht.2.1 ht.2.2.1 he
        · have hU : At u u.pc (groupScanFacts scan first batch cta) := by
            refine ⟨rfl, hSub, hAcc, hAdvance.2.trans ht.2.2.2.1, ?_⟩
            exact Epilogue.holdsSchedulerFrame ht.2.2.2.2 hRegs groupScanRegs
          have hPc := hAdvance.1
          have hUlo : site.head + 5 ≤ u.pc := by omega
          have hUhi : u.pc ≤ site.compare + 2 := by omega
          have hUn : u.pc ≠ site.head := by omega
          have hCnt := ih vs.length hSmaller first rfl hFirst (.inr ⟨hUlo, hUhi⟩) hU hw
          change countedUntil cutoff vs ≤ scanRank site batch first u.pc at hCnt
          have hMon : scanRank site batch first u.pc + 1 ≤ scanRank site batch first s.pc := by
            simp only [scanRank, ite_eq_right hsNotHead, ite_eq_right hUn]
            omega
          have hTest : decide ((visit kernel l g s (some e)).pc < cutoff) = true :=
            decide_eq_true hsCut
          rw [countedUntil, List.takeWhile_cons, ite_eq_left hTest]
          simp only [List.filterMap_cons, visit_ev, List.countP_cons]
          change countedUntil cutoff vs + (if e.counts then 1 else 0) ≤ _
          split <;> omega
        · have hCnt : countedUntil cutoff vs ≤ 1 := countFaultedScan hFault.2 hw
          have hTest : decide ((visit kernel l g s (some e)).pc < cutoff) = true :=
            decide_eq_true hsCut
          rw [countedUntil, List.takeWhile_cons, ite_eq_left hTest]
          simp only [List.filterMap_cons, visit_ev, List.countP_cons]
          change countedUntil cutoff vs + (if e.counts then 1 else 0) ≤ _
          simp only [scanRank, ite_eq_right hsNotHead]
          split <;> omega
      | @last s e he =>
        have hBudget : 1 ≤ scanRank site batch first s.pc := by simp [scanRank]; omega
        simpa [countedUntil, hsCut, visit_pc, visit_ev] using
          (List.countP_le_length (p := Event.counts) (l := [e])).trans hBudget

/-- All counted events of either group search are bounded from any decoded loop-head prefix.
The budget includes early suspension and a final load fault. -/
theorem groupScanPrefixBound (scan : GroupScan) {l : Launch} {g first batch cta : Nat}
    (hBatch : batch + 31 < 2 ^ 31) (hCta : cta + 1 < 2 ^ 31) (hFirst : first ≤ batch)
    {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s (scanSite scan).head (groupScanFacts scan first batch cta))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    countedUntil ((scanSite scan).compare + 3) vs ≤ 64 * (batch - first + 1) := by
  have h := scanCountLe scan hBatch hCta vs.length first rfl hFirst (.inl hs.1)
    (by simpa only [hs.1] using hs) hw
  simpa [scanRank, hs.1] using h

end
end PTX.Kernels.TmlFa4Fwd.Mma
