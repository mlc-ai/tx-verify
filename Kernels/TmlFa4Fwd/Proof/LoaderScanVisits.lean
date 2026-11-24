-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaScanPrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Mma

noncomputable section

/-- A loader branch already passed by the lane cannot be visited again when
no frozen backedge crosses back over it. -/
theorem noLaterLoaderCounter {l : Launch} {g pc : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hp : pc < s.pc)
    (hBack : loaderBackEdges.all (fun (p, target) => !(pc < p && target ≤ pc)) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) : loaderVisitsAt pc vs = 0 := by
  have step {t u : TState} {e : Option Event} (hpc : pc < t.pc)
      (hRole : 174 ≤ t.pc ∧ t.pc < 1906)
      (h : WStep kernel Assumptions.all l g t e u) : pc < u.pc := by
    rcases h with ⟨_, hTau⟩ | ⟨ev, _, he⟩
    · by_contra hNot
      have hLe : u.pc ≤ pc := by omega
      have hm := loaderTauBackEdge hRole.1 hRole.2 (by omega) hTau
      have hb := List.all_eq_true.mp hBack _ hm
      simp [hpc, hLe] at hb
    · have he' : EStep kernel [] l g t ev (some u) := by
        obtain ⟨tmp, hout, hf⟩ := he
        exact ⟨tmp, by rwa [← loaderOutCore hRole.1 hRole.2], hf⟩
      rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with he | he <;> omega
  have cons {t : TState} (hpc : pc < t.pc) (e : Option Event) (tail : List Visit)
      (hTail : (174 ≤ t.pc ∧ t.pc < 1906) → loaderVisitsAt pc tail = 0) :
      loaderVisitsAt pc (visit kernel l g t e :: tail) = 0 := by
    unfold loaderVisitsAt loaderVisits
    rw [List.takeWhile_cons, visit_pc]
    split
    · rename_i hRole
      rw [List.countP_cons, visit_pc]
      have hTest : (t.pc == pc) = false := by simpa only [beq_eq_false_iff_ne] using hpc.ne'
      simp only [hTest, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact hTail (of_decide_eq_true hRole)
    · rfl
  induction hw with
  | stop => rfl
  | tau ht _ ih => exact cons hp none _ (fun hr => ih (step hp hr (.inl ⟨rfl, ht⟩)))
  | ev he _ ih => exact cons hp (some _) _ (fun hr => ih (step hp hr (.inr ⟨_, rfl, he⟩)))
  | last => exact cons hp (some _) [] (fun _ => rfl)

private theorem loaderScanRange (scan : Fin 2) :
    let site := scanSite (if scan.val = 0 then .loaderSelect else .loaderDrain)
    174 ≤ site.head ∧ site.head + 5 ≤ site.compare ∧ site.compare + 2 < 1906 := by
  fin_cases scan <;> decide

private theorem loaderScanNoReentry (scan : Fin 2) :
    let site := scanSite (if scan.val = 0 then .loaderSelect else .loaderDrain)
    loaderBackEdges.all (fun (pc, target) => !(site.compare + 2 < pc && target ≤ site.compare + 2))
      = true := by
  fin_cases scan <;> decide

private theorem scanBranchCount (which : Fin 2) {l : Launch} {g batch cta : Nat}
    (hBatch : batch + 31 < 2 ^ 31) (hCta : cta + 1 < 2 ^ 31) :
    let scan := if which.val = 0 then GroupScan.loaderSelect else GroupScan.loaderDrain
    let site := scanSite scan
    ∀ fuel first {s : TState} {es : List Event} {vs : List Visit}, vs.length = fuel →
      first ≤ batch → (s.pc = site.head ∨ (site.head + 5 ≤ s.pc ∧ s.pc ≤ site.compare + 2)) →
      At s s.pc (groupScanFacts scan first batch cta) →
      Walk kernel Assumptions.all l g s es vs →
      loaderVisitsAt (site.compare + 2) vs ≤ 8 * (batch - first + 1) +
        if s.pc = site.head then 0 else 1 := by
  let scan := if which.val = 0 then GroupScan.loaderSelect else GroupScan.loaderDrain
  let site := scanSite scan
  let branch := site.compare + 2
  have hRange := loaderScanRange which
  have hBack := loaderScanNoReentry which
  change 174 ≤ site.head ∧ site.head + 5 ≤ site.compare ∧ branch < 1906 at hRange
  change loaderBackEdges.all (fun (pc, target) => !(branch < pc && target ≤ branch)) = true at hBack
  dsimp only
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    change ∀ m < fuel, ∀ first {s : TState} {es : List Event} {vs : List Visit},
      vs.length = m → first ≤ batch →
      (s.pc = site.head ∨ (site.head + 5 ≤ s.pc ∧ s.pc ≤ branch)) →
      At s s.pc (groupScanFacts scan first batch cta) →
      Walk kernel Assumptions.all l g s es vs →
      loaderVisitsAt branch vs ≤ 8 * (batch - first + 1) +
        if s.pc = site.head then 0 else 1 at ih
    intro first s es vs hLen hFirst hPc hs hw
    change (s.pc = site.head ∨ (site.head + 5 ≤ s.pc ∧ s.pc ≤ branch)) at hPc
    change loaderVisitsAt branch vs ≤ 8 * (batch - first + 1) +
      if s.pc = site.head then 0 else 1
    rcases hPc with hHead | ⟨hLo, hHi⟩
    · have hAt : At s site.head (groupScanFacts scan first batch cta) := ⟨hHead, hs.2⟩
      obtain ⟨u, hr, hu⟩ := advanceGroupScanFramed scan (g := g) (by omega) (by omega) hAt
      rw [ite_eq_left hHead]
      by_cases hDone : batch ≤ first + 31
      · rw [ite_eq_left hDone] at hu
        have hLast : At u site.compare [(site.work, b32 (cta + 1)), (site.cta, b32 cta)] :=
          hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.1, trivial⟩
        obtain ⟨v, hv, hV⟩ := exhaustedGroupScan scan (g := g) hCta hLast
        rcases loaderLocalWalkCut (run_comp hr hv) hw with hShort | ⟨pre, tail, rfl, hN, hTail⟩
        · exact (loaderVisitsAt_le_length ..).trans (by omega)
        · have hEnd : v.pc = branch + 1 := by
            have h := hV.1
            change v.pc = site.compare + 3 at h
            dsimp only [branch]
            omega
          have hPast := noLaterLoaderCounter (pc := branch) (by omega) hBack hTail
          have hSum := loaderVisitsAt_le_append branch pre tail
          omega
      · rw [ite_eq_right hDone, Nat.min_eq_left (by omega : first + 31 ≤ batch)] at hu
        rcases loaderLocalWalkCut hr hw with hShort | ⟨pre, tail, rfl, hN, hTail⟩
        · exact (loaderVisitsAt_le_length ..).trans (by omega)
        · have hPc := hu.1
          change u.pc = site.head + 5 at hPc
          have hURange : site.head + 5 ≤ u.pc ∧ u.pc ≤ branch := by
            dsimp only [branch]
            omega
          have ha := ih tail.length (by simp only [List.length_append, hN] at hLen; omega)
            (first + 31) rfl (by omega) (.inr hURange) ⟨rfl, hu.2.1,
              hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.2⟩ hTail
          change loaderVisitsAt branch tail ≤ _ at ha
          have hOver := loaderVisitsAt_le_append branch pre tail
          split at ha <;> omega
    · have hNe : s.pc ≠ site.head := by omega
      rw [ite_eq_right hNe]
      have hRole : 174 ≤ s.pc ∧ s.pc < 1906 := by omega
      have addVisit (e : Option Event) (vs : List Visit) :
          loaderVisitsAt branch (visit kernel l g s e :: vs) ≤ loaderVisitsAt branch vs + 1 := by
        have h := loaderVisitsAt_le_append branch [visit kernel l g s e] vs
        simpa [Nat.add_comm] using h
      cases hw with
      | stop => exact Nat.zero_le _
      | @tau s t es vs ht hw =>
        have hSmaller : vs.length < fuel := by simp only [List.length_cons] at hLen; omega
        by_cases hEnd : s.pc = branch
        · obtain ⟨hEnter | hExit, hSub, hAcc, hFault, hRegs⟩ :=
            scanEndTau scan hEnd hs.2.1 hs.2.2.1 ht
          · have hT : At t t.pc (groupScanFacts scan first batch cta) :=
              ⟨rfl, hSub.trans hs.2.1, hAcc.trans hs.2.2.1, hFault.trans hs.2.2.2.1,
                hRegs.symm ▸ hs.2.2.2.2⟩
            have hNext := ih vs.length hSmaller first rfl hFirst (.inl hEnter) hT hw
            change loaderVisitsAt branch vs ≤ _ at hNext
            rw [ite_eq_left hEnter, Nat.add_zero] at hNext
            exact (addVisit none vs).trans (Nat.add_le_add_right hNext 1)
          · change t.pc = branch + 1 at hExit
            have hZero := noLaterLoaderCounter (pc := branch) (by omega) hBack hw
            have h := addVisit none vs
            rw [hZero] at h
            exact h.trans (by omega)
        · have hLt : s.pc < branch := by omega
          obtain ⟨hNext, hLimit, hSub, hAcc, hFault, hRegs⟩ :=
            scanBodyTau scan hLo hLt hs.2.1 hs.2.2.1 ht
          have hT : At t t.pc (groupScanFacts scan first batch cta) :=
            ⟨rfl, hSub.trans hs.2.1, hAcc.trans hs.2.2.1, hFault.trans hs.2.2.2.1,
              Epilogue.holdsSchedulerFrame hs.2.2.2.2 hRegs (by
                simp [groupScanFacts, scanFrame])⟩
          rw [visitsBeforeBranch hRole hLt]
          have ha := ih vs.length hSmaller first rfl hFirst (.inr ⟨by omega, hLimit⟩) hT hw
          change loaderVisitsAt branch vs ≤ _ at ha
          split at ha <;> omega
      | @ev s t e es vs he hw =>
        have hSmaller : vs.length < fuel := by simp only [List.length_cons] at hLen; omega
        have hLt : s.pc < branch := by
          by_contra h
          have hPc : s.pc = branch := by omega
          obtain ⟨ins, hCode, hLocal, _⟩ := estep_event_source he
          have hBranch : ∃ ins, kernel.code[branch]? = some ins ∧ ins.op.isLocal = true := by
            fin_cases which
            · exact ⟨_, Flow.code_287, rfl⟩
            · exact ⟨_, Flow.code_1847, rfl⟩
          obtain ⟨i, hi, hLoc⟩ := hBranch
          rw [hPc, hi] at hCode
          obtain rfl := Option.some.inj hCode
          rw [hLoc] at hLocal
          cases hLocal
        rw [visitsBeforeBranch hRole hLt]
        obtain ⟨hAdv | hFault, hSub, hAcc, hRegs⟩ :=
          scanBodyEvent scan hLo hLt hs.2.1 hs.2.2.1 he
        · have hT : At t t.pc (groupScanFacts scan first batch cta) :=
            ⟨rfl, hSub, hAcc, hAdv.2.trans hs.2.2.2.1,
              Epilogue.holdsSchedulerFrame hs.2.2.2.2 hRegs (by
                simp [groupScanFacts, scanFrame])⟩
          have ha := ih vs.length hSmaller first rfl hFirst (.inr ⟨by omega, by omega⟩) hT hw
          change loaderVisitsAt branch vs ≤ _ at ha
          split at ha <;> omega
        · have hf : t.fault ≠ none := by
            cases h : t.fault
            · simp [h] at hFault
            · simp
          rw [pipelineStopped hw hf (by omega) (by omega)]
          exact Nat.zero_le _
      | @last s e he =>
        have h := addVisit (some e) []
        change loaderVisitsAt branch (visit kernel l g s (some e) :: []) ≤ 1 at h
        exact h.trans (by omega)

/-- The two loader request scans consume a finite number of branch visits from
their independently initialized batch counters. -/
theorem loaderScanBranchBudget (which : Fin 2) {l : Launch} {g batch cta : Nat}
    (hBatch : batch + 31 < 2 ^ 31) (hCta : cta + 1 < 2 ^ 31) {s : TState}
    {es : List Event} {vs : List Visit}
    (hs : let scan := if which.val = 0 then GroupScan.loaderSelect else GroupScan.loaderDrain
      At s (scanSite scan).head (groupScanFacts scan 0 batch cta))
    (hw : Walk kernel Assumptions.all l g s es vs) :
    let scan := if which.val = 0 then GroupScan.loaderSelect else GroupScan.loaderDrain
    loaderVisitsAt ((scanSite scan).compare + 2) vs ≤ 8 * (batch + 1) := by
  have h := scanBranchCount which (l := l) (g := g) hBatch hCta vs.length 0 rfl
    (Nat.zero_le _) (.inl hs.1) ⟨rfl, hs.2⟩ hw
  simpa only [hs.1, ↓reduceIte, Nat.sub_zero, Nat.add_zero] using h

end
end PTX.Kernels.TmlFa4Fwd.Loader
