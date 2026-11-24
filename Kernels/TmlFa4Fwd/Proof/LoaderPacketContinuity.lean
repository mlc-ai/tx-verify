-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPacketSites
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.ContinuingEvent
import Lemmas.Step.CtaBar
import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private theorem backToPacketEntry (earlier next : Fin 6) :
    copyPacketFirst earlier < copyPacketFirst next →
    copyCommitPc earlier < copyPacketFirst next := by
  fin_cases earlier <;> fin_cases next <;> decide

private theorem bulkInsideLoader :
    OpPcsFast kernel.code bulkOp (List.range' 174 (1906 - 174)) = true := by
  decide +kernel

private theorem returningCommitKind {l : Launch} {g : Nat} {t u : TState} {e : Event}
    (site : Fin 6) (hp : t.pc = copyCommitPc site)
    (he : EStep kernel Assumptions.all l g t e (some u)) : e.kind = .asyncCommit := by
  have hb := loaderPacketBounds site
  obtain ⟨tmpl, ho, hf⟩ := he
  have hr : EStep kernel [] l g t e (some u) :=
    ⟨tmpl, by rwa [← loaderOutCore (by omega) (by omega)], hf⟩
  obtain ⟨ins, hIns, _, hFire⟩ := estep_event_source hr
  rw [hp, (copyCommitCode site).1] at hIns
  obtain rfl := Option.some.inj hIns.symm
  simp only [eventTmpl, cpAsyncTmpl, Fires] at hFire
  rw [hFire.1]

private theorem withinUncommittedPacket {l : Launch} {g : Nat} {t : TState}
    {es : List Event} {visits : List Visit}
    (site : Fin 6) (hw : Walk kernel Assumptions.all l g t es visits)
    (hLo : copyPacketFirst site < t.pc) (hHi : t.pc ≤ copyCommitPc site)
    {j : Nat} {e : Event} (he : es[j]? = some e)
    (hNone : ∀ k < j, es[k]? ≠ some ⟨copyCommitPc site, .asyncCommit⟩) :
    (copyPacketFirst site < e.pc ∧ e.pc ≤ copyCommitPc site) ∧ t.pc ≤ e.pc := by
  have hb := loaderPacketBounds site
  induction hw generalizing j with
  | stop => simp at he
  | @tau t u es visits ht hw ih =>
    have hLt : t.pc < copyCommitPc site := by
      by_contra! hn
      have hEq : t.pc = copyCommitPc site := by omega
      have hc := hEq.symm ▸ (copyCommitCode site).1
      have ht' : Tau kernel [] l g t u := by
        unfold Tau at *
        rwa [← loaderOutCore (by omega) (by omega)]
      exact tau_core_not_event hc rfl ht'
    have hu := packetTauNext hLo.le hLt ht
    obtain ⟨hRange, hFrom⟩ := ih (by omega) (by omega) he hNone
    exact ⟨hRange, by omega⟩
  | @ev t u f es visits ht hw ih =>
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      rw [estep_source_pc ht]
      exact ⟨⟨hLo, hHi⟩, le_rfl⟩
    | succ j =>
      have hLt : t.pc < copyCommitPc site := by
        by_contra! hn
        have hp : t.pc = copyCommitPc site := by omega
        have hKind := returningCommitKind site hp ht
        have hPc := (estep_source_pc ht).trans hp
        have hEvent : f = ⟨copyCommitPc site, .asyncCommit⟩ := by
          cases f
          simp only [Event.mk.injEq]
          exact ⟨hPc, hKind⟩
        exact hNone 0 (by omega) (by simp [hEvent])
      have hu := packetEventNext (by omega) (by omega) ht
      obtain ⟨hRange, hFrom⟩ := ih (by omega) (by omega) he
        (fun k hk => hNone (k + 1) (by omega))
      exact ⟨hRange, by omega⟩
  | @last t f ht =>
    cases j with
    | zero =>
      obtain rfl := Option.some.inj he
      rw [estep_source_pc ht]
      exact ⟨⟨hLo, hHi⟩, le_rfl⟩
    | succ j => simp at he

/-- A walk reaching the commit from its packet entry performs an actual issue there. -/
theorem packetEntryIssue {l : Launch} {g : Nat} {t : TState} {events : List Event}
    {visits : List Visit} (site : Fin 6)
    (hw : Walk kernel Assumptions.all l g t events visits)
    (ht : t.pc = copyPacketFirst site)
    (hReach : ∃ v ∈ visits, v.pc = copyCommitPc site) :
    ∃ e, events[0]? = some e ∧ e.pc = copyPacketFirst site := by
  have hb := loaderPacketBounds site
  have hEntry : packetPlanePc site 0 false = copyPacketFirst site := by
    fin_cases site <;> decide
  have hc := packetFullCode site 0 false
  rw [hEntry, ← ht] at hc
  cases hw with
  | stop => simp at hReach
  | @tau _ u _ _ h _ =>
    have hCore : Tau kernel [] l g t u := by
      unfold Tau at *
      rwa [← loaderOutCore (by omega) (by omega)]
    exact (tau_core_not_event hc rfl hCore).elim
  | ev h _ => exact ⟨_, rfl, (estep_source_pc h).trans ht⟩
  | last h => exact ⟨_, rfl, (estep_source_pc h).trans ht⟩

/-- Every earlier copy on the lane has an intervening commit before the first
copy at a packet entry. The result uses actual issue positions and tolerates
any earlier visits to the same decoded packet. -/
theorem packetEntrySeparatesCopies {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (site : Fin 6)
    {g i j : Nat} {spec : AsyncCopy.Spec} {e : Event}
    (hCopy : X.Copy (g, i) spec) (he : X.get (g, j) = some e)
    (hEntry : e.pc = copyPacketFirst site) (hOrder : i < j) :
    ∃ k packet, i < k ∧ k < j ∧ X.get (g, k) = some ⟨copyCommitPc packet, .asyncCommit⟩ := by
  obtain ⟨pc, hc⟩ := hCopy
  rcases get_source hX hc with ⟨_, hf⟩ | ⟨s, ins, o, _, hCode, hFires⟩
  · cases hf
  have hBulk := OpPcsFast.mem bulkInsideLoader hCode (fires_bulk_op hFires rfl)
  obtain ⟨hLo, hHi⟩ := List.mem_range'_1.mp hBulk
  change 174 ≤ pc at hLo
  change pc < 1906 at hHi
  have hJ := (List.getElem?_eq_some_iff.mp (show (X.tr g)[j]? = some e from he)).1
  obtain ⟨_, hr⟩ := hX.thr g (Step.CtaBar.thread_lt_of_get hX hc)
  obtain ⟨t, u, hStep, hRun⟩ := hr.after_event hc (by omega)
  have hPc : t.pc = pc := (estep_source_pc hStep).symm
  have hCopyAt := loaderCopyEventSite (by omega) (by omega) hStep rfl
  obtain ⟨prior, hFirst, hCommit⟩ :=
    loaderCopyPcInPacket hLo hHi (hPc ▸ hCopyAt)
  have hu : u.pc = pc + 1 := by
    rcases packetEventNext (by omega) (by omega) hStep with hAdvance | ⟨_, hNoCopy⟩
    · exact hPc ▸ hAdvance
    · rw [hCopyAt] at hNoCopy
      cases hNoCopy
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hRun
  by_contra hNone
  have hj : ((X.tr g).drop (i + 1))[j - (i + 1)]? = some e := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le (by omega : i + 1 ≤ j)]
  obtain ⟨hWindow, _⟩ := withinUncommittedPacket prior hWalk (by omega) (by omega) hj (by
    intro k hk hGet
    rw [List.getElem?_drop] at hGet
    exact hNone ⟨i + 1 + k, prior, by omega, by omega, hGet⟩)
  rw [hEntry] at hWindow
  exact (Nat.not_lt_of_ge hWindow.2) (backToPacketEntry prior site hWindow.1)

variable {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    (site : Fin 6) {g i j pc qc : Nat} {src dst : AsyncCopy.Spec}
    (hi : X.get (g, i) = some ⟨pc, .copy src⟩) (hj : X.get (g, j) = some ⟨qc, .copy dst⟩)
    (hIn : copyPacketFirst site ≤ pc ∧ pc < copyCommitPc site)
include hX site hi hj hIn

/-- The later same-group copy stays inside the earlier copy’s uncommitted packet. -/
theorem packetCopyPcOrderAndWindow (hGroup : SameAsyncGroup X (g, i) (g, j)) :
    pc < qc ∧ qc ≤ copyCommitPc site := by
  have hBounds := loaderPacketBounds site
  have hLT : i < j := hGroup.2.2.2.1
  have hJ := (List.getElem?_eq_some_iff.mp (show (X.tr g)[j]? = some _ from hj)).1
  obtain ⟨_, hr⟩ := hX.thr g (Step.CtaBar.thread_lt_of_get hX hi)
  obtain ⟨t, u, hStep, hRun⟩ := hr.after_event hi (by omega)
  have hPc : t.pc = pc := (estep_source_pc hStep).symm
  have hCopy := loaderCopyEventSite (by omega) (by omega) hStep rfl
  have hu : u.pc = pc + 1 := by
    rcases packetEventNext (by omega) (by omega) hStep with hNext | ⟨_, hNo⟩
    · rwa [hPc] at hNext
    · rw [hCopy] at hNo
      cases hNo
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hRun
  have hGet : ((X.tr g).drop (i + 1))[j - (i + 1)]? = some ⟨qc, .copy dst⟩ := by
    rwa [List.getElem?_drop, Nat.add_sub_of_le (by omega : i + 1 ≤ j)]
  obtain ⟨hRange, hAfter⟩ := withinUncommittedPacket site hWalk (by omega) (by omega) hGet (by
    intro k hk hCommit
    rw [List.getElem?_drop] at hCommit
    exact hGroup.2.2.2.2 (i + 1 + k) _ (by omega) (by omega) hCommit)
  change u.pc ≤ qc at hAfter
  exact ⟨by omega, hRange.2⟩

/-- Two ordered ordinary-copy issues in one uncommitted packet have strictly increasing PCs. -/
theorem packetCopyPcOrder (hGroup : SameAsyncGroup X (g, i) (g, j)) :
    pc < qc := by
  exact (packetCopyPcOrderAndWindow hX site hi hj hIn hGroup).1

end
end PTX.Kernels.TmlFa4Fwd.Loader
