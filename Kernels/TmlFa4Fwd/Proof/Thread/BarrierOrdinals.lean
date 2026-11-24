-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarriers
import Kernels.TmlFa4Fwd.Proof.PrologueGenerationZero
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow Prologue

/-- The index of a rendezvous among all CTA barrier events in the lane. -/
def barrierOrdinal (X : Execution) (i : EvId) : Nat :=
  ((X.tr i.1).take i.2).countP Execution.isBar

theorem commonBeforeRoleEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e) (hPc : 173 < e.pc) :
    ∃ n < j, X.IsBarrier (g,n) 0 none 173 := by
  have hg := event_thread_lt hX he
  by_cases hw : warpIndex l g = 0
  · obtain ⟨n, hn, hf, hb, _, _⟩ :=
      warp0InitializerPrefix hp hX hg hw he (Nat.le_of_lt hPc)
    have hn' : n ≠ j := by
      intro hEq
      subst j
      obtain rfl := Option.some.inj (hf.symm.trans he)
      exact (by decide : ¬ 173 < 172) hPc
    have hb' : n + 1 ≠ j := by
      intro hEq
      subst j
      obtain rfl := Option.some.inj (hb.symm.trans he)
      exact (by decide : ¬ 173 < 173) hPc
    exact ⟨n + 1, by omega, hb⟩
  · obtain ⟨hj, hb, _⟩ := nonzeroStartupBar hp hX hg (Nat.pos_of_ne_zero hw) he hPc
    exact ⟨4, hj, hb⟩

private theorem commonOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g j : Nat}
    (he : X.IsBarrier (g,j) 0 none 173) : barrierOrdinal X (g,j) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e hMem
  cases e with
  | mk site kind =>
    cases kind <;> simp only [Execution.isBar, Bool.false_eq_true, not_false_eq_true,
      not_true_eq_false]
    rename_i id count mode
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hMem
    have hLt : k < j :=
      (List.getElem?_eq_some_iff.mp hk).1.trans_le (List.length_take_le _ _)
    rw [List.getElem?_take_of_lt hLt] at hk
    have hGet : X.get (g,k) = some ⟨site, .bar id count mode⟩ := hk
    obtain ⟨hSite, _, hMode, _, hCount, hId, _⟩ := actualNamedBarrier hp hX hGet
    have hLow : 173 ≤ site := by
      simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
      omega
    have hg := event_thread_lt hX (show X.get (g,j) = some ⟨173, .bar 0 none .sync⟩ from he)
    rcases Nat.eq_or_lt_of_le hLow with rfl | hPast
    · obtain rfl := hCount.mpr rfl
      obtain rfl := hId rfl
      obtain rfl := hMode
      have hSame := commonStartupUnique hX hg hGet he
      omega
    · obtain ⟨n, hn, hb⟩ := commonBeforeRoleEvent hp hX hGet hPast
      have hSame := commonStartupUnique hX hg hb he
      omega

/-- The common synchronization is the only CTA barrier that can occur at ordinal zero. -/
theorem BarrierArrival.ordinalZeroIff {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {id : Nat} {count : Option Nat} {mode : BarMode}
    (h : BarrierArrival X i id count mode) : barrierOrdinal X i = 0 ↔ id = 0 := by
  obtain ⟨g, j⟩ := i
  obtain ⟨⟨site, _⟩, he, rfl⟩ := h
  obtain ⟨hSite, _, hMode, _, hCount, hId, _⟩ := actualNamedBarrier hp hX he
  have hLow : 173 ≤ site := by
    simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
    omega
  rcases Nat.eq_or_lt_of_le hLow with rfl | hPast
  · obtain rfl := hCount.mpr rfl
    obtain rfl := hId rfl
    obtain rfl := hMode
    exact iff_of_true (commonOrdinal hp hX he) rfl
  · obtain ⟨n, hn, hb⟩ := commonBeforeRoleEvent hp hX he hPast
    have hEarlier := countP_take_succ (p := Execution.isBar)
      (show X.get (g,n) = some ⟨173, .bar 0 none .sync⟩ from hb) rfl
    have hLe := countP_take_mono Execution.isBar (X.tr g) (show n + 1 ≤ j by omega)
    rw [hEarlier] at hLe
    have hNonzero : barrierOrdinal X (g,j) ≠ 0 := by
      change ((X.tr g).take j).countP Execution.isBar ≠ 0
      omega
    have hNamed : id ≠ 0 := by
      rintro rfl
      have hN := actualNamedBarrierCountById hp hX he
      have hEq : count = none := hN
      exact (Nat.ne_of_gt hPast) (hCount.mp hEq)
    exact iff_of_false hNonzero hNamed

/-- A disagreement at the same barrier ordinal can only involve role rendezvous. -/
theorem BarrierArrival.nonstartupOfDisagreement {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {id id' : Nat} {count count' : Option Nat} {mode mode' : BarMode}
    (he : BarrierArrival X i id count mode) (hf : BarrierArrival X j id' count' mode')
    (hOrdinal : barrierOrdinal X i = barrierOrdinal X j)
    (hDiff : id ≠ id' ∨ mode ≠ mode') : id ≠ 0 ∧ id' ≠ 0 := by
  have hBoth : id = 0 ↔ id' = 0 := by
    rw [← he.ordinalZeroIff hp hX, ← hf.ordinalZeroIff hp hX, hOrdinal]
  have hSync {i : EvId} {count : Option Nat} {mode : BarMode}
      (hs : BarrierArrival X i 0 count mode) : mode = .sync := by
    obtain ⟨⟨site, _⟩, hGet, rfl⟩ := hs
    have hCount : count = none := actualNamedBarrierCountById hp hX hGet
    obtain ⟨_, _, hMode, _, hSite, _⟩ := actualNamedBarrier hp hX hGet
    obtain rfl := hSite.mp hCount
    exact hMode
  have hNot : id ≠ 0 := by
    intro hZero
    have hZero' := hBoth.mp hZero
    rcases hDiff with hId | hMode
    · exact hId (hZero.trans hZero'.symm)
    · exact hMode ((hSync (hZero ▸ he)).trans (hSync (hZero' ▸ hf)).symm)
  exact ⟨hNot, fun hz => hNot (hBoth.mpr hz)⟩

private theorem namedBarrierAvoidsRegisterHint :
    namedBarrierSites.all (fun site => !(registerHintSites.contains site)) = true := by
  decide +kernel

/-- Beyond startup, the loader and drain have no CTA rendezvous, and the MMA role
uses the same synchronous allocation barrier wherever it has a rendezvous. -/
theorem BarrierArrival.allocationForMmaOrDrain {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {id : Nat} {count : Option Nat} {mode : BarMode}
    (he : BarrierArrival X i id count mode) (hNamed : id ≠ 0) (hw : 12 ≤ warpIndex l i.1) :
    warpIndex l i.1 = 12 ∧ id = 2 ∧ count = some 416 ∧ mode = .sync := by
  obtain ⟨⟨site, _⟩, hGet, rfl⟩ := he
  obtain ⟨hSites, hCount, hMode, _, _, hZero, hTwo⟩ := actualNamedBarrier hp hX hGet
  have hNotCommon : site ≠ 173 := fun h => hNamed (hZero h)
  have hLate : 173 < site := by
    simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSites
    omega
  have hNotHint : site ∉ registerHintSites := by
    simpa using List.all_eq_true.mp namedBarrierAvoidsRegisterHint site hSites
  have hRole := roleBodyPcOfEvent hp hX hGet hLate hNotHint
  have hResult : warpIndex l i.1 = 12 ∧ (site = 1910 ∨ site = 2764) := by
    change roleBodyPc (warpIndex l i.1) site at hRole
    unfold roleBodyPc at hRole
    simp only [namedBarrierSites, List.mem_cons, List.not_mem_nil, or_false] at hSites
    rcases hRole with hEq | hRole
    · omega
    · split_ifs at hRole <;> omega
  have hValue : count = some 416 := by
    rcases hResult.2 with rfl | rfl <;> exact hCount
  refine ⟨hResult.1, hTwo hValue, hValue, ?_⟩
  rcases hResult.2 with rfl | rfl <;> exact hMode

end PTX.Kernels.TmlFa4Fwd.Thread
