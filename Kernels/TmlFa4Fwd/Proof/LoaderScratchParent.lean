-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderScratchRank
public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixRank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- The three warm-up and three steady-stage scratch loops are under their ring backedge.
The priming scratch loops have no enclosing backedge. -/
def scratchParent (i : Fin 9) : Nat :=
  if i.val < 3 then 0 else if i.val < 6 then 1352 else 1743

def loaderVisitsAt (pc : Nat) (visits : List Visit) : Nat :=
  (loaderVisits visits).countP (fun v => v.pc == pc)

private def scratchTargets : List Nat :=
  (List.finRange 9).map fun i => (loaderScratchLoop i).back

private def avoidsScratchTail : Op → Bool
  | .bra target _ => !scratchTargets.contains target
  | .brx .. => false
  | _ => true

private theorem noScratchTailTarget :
    ((kernel.code.drop 174).take (1906 - 174)).all (fun i => avoidsScratchTail i.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem scratchTailFound (i : Fin 9) : (loaderScratchLoop i).back ∈ scratchTargets := by
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

private theorem tailTargetGuard {op : Op} {pc tail : Nat}
    (hOk : avoidsScratchTail op = true) (hMem : tail ∈ scratchTargets) :
    ¬ BrxTarget op tail ∧ (nextPc op pc = tail → pc + 1 = tail) := by
  cases op <;> simp only [avoidsScratchTail, Bool.false_eq_true] at hOk
  case bra target uni =>
    refine ⟨by simp [BrxTarget], ?_⟩
    intro ht
    change target = tail at ht
    subst target
    simp [hMem] at hOk
  all_goals exact ⟨by simp [BrxTarget], id⟩

private theorem coreSilent {l : Launch} {g : Nat} {s u : TState}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906)
    (ht : Tau kernel Assumptions.all l g s u) : Tau kernel [] l g s u := by
  unfold Tau at ht ⊢
  rwa [← loaderOutCore hLo hHi]

private theorem eventMovesForward {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc ∨ u.pc = s.pc + 1 := by
  have he' : EStep kernel [] l g s e (some u) := by
    obtain ⟨tmpl, ht, hf⟩ := he
    exact ⟨tmpl, by rwa [← loaderOutCore hLo hHi], hf⟩
  exact (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2

private theorem stepIntoTail (i : Fin 9) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906)
    (hPc : u.pc = (loaderScratchLoop i).back)
    (h : WStep kernel Assumptions.all l g s e u) : s.pc = u.pc ∨ s.pc + 1 = u.pc := by
  rcases h with ⟨-, ht⟩ | ⟨_, -, he⟩
  · have ht' := coreSilent hLo hHi ht
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    have hGet : ((kernel.code.drop 174).take (1906 - 174))[s.pc - 174]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    have hOk := List.all_eq_true.mp noScratchTailTarget ins (List.mem_of_getElem? hGet)
    obtain ⟨hBrx, hF⟩ := tailTargetGuard (pc := s.pc) hOk (scratchTailFound i)
    right
    rcases tau_core_frame hc ht' with rfl | h
    · rfl
    · rw [hPc]
      exact hF ((h.pc.resolve_right (by rw [hPc]; exact hBrx)).symm.trans hPc)
  · exact (eventMovesForward hLo hHi he).imp Eq.symm Eq.symm

private theorem scratchIntervals (i : Fin 9) :
    let loop := loaderScratchLoop i
    loaderBackEdges.all (fun edge =>
      (!(loop.back < edge.1 && edge.2 ≤ loop.back) || edge.1 == scratchParent i) &&
      (!(loop.head ≤ edge.1 && edge.1 ≤ loop.back) || loop.head ≤ edge.2)) = true := by
  fin_cases i <;> decide

private theorem enclosingBackedge (i : Fin 9) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906)
    (hs : (loaderScratchLoop i).back < s.pc) (hu : u.pc ≤ (loaderScratchLoop i).back)
    (h : WStep kernel Assumptions.all l g s e u) : s.pc = scratchParent i := by
  rcases h with ⟨-, ht⟩ | ⟨_, -, he⟩
  · have hm := loaderTauBackEdge hLo hHi (by omega) ht
    have ho := List.all_eq_true.mp (scratchIntervals i) (s.pc, u.pc) hm
    simpa [hs, hu] using (Bool.and_eq_true_iff.mp ho).1
  · rcases eventMovesForward hLo hHi he with hp | hp <;> omega

private theorem scratchCannotLeaveBefore (i : Fin 9) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event}
    (hs : (loaderScratchLoop i).head ≤ s.pc ∧ s.pc ≤ (loaderScratchLoop i).back)
    (h : WStep kernel Assumptions.all l g s e u) : (loaderScratchLoop i).head ≤ u.pc := by
  have hB := scratchLoopBounds i
  have hLo : 174 ≤ s.pc := by omega
  have hHi : s.pc < 1906 := by omega
  by_contra hu
  rcases h with ⟨-, ht⟩ | ⟨_, -, he⟩
  · have hm := loaderTauBackEdge hLo hHi (by omega) ht
    have ho := List.all_eq_true.mp (scratchIntervals i) (s.pc, u.pc) hm
    exact hu (by simpa [hs.1, hs.2] using (Bool.and_eq_true_iff.mp ho).2)
  · rcases eventMovesForward hLo hHi he with hp | hp <;> omega

private def scratchFuel (loop : ScratchLoop) (s : TState) : Nat :=
  if s.pc < loop.head then 2 else if s.pc ≤ loop.back then scratchBudget loop s else 0

private theorem scratchFuelRange (loop : ScratchLoop) (s : TState) :
    scratchFuel loop s ≤ 2 := by
  unfold scratchFuel
  split
  · decide
  · split
    · exact (scratchBudgetRange loop s).2
    · decide

private theorem scratchParentStep (i : Fin 9) {l : Launch} {g : Nat}
    {s u : TState} {e : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906)
    (hSeed : s.pc = (loaderScratchLoop i).back →
      s.regs (loaderScratchLoop i).seed = some (.pred false))
    (h : WStep kernel Assumptions.all l g s e u) :
    let loop := loaderScratchLoop i
    (u.pc = loop.back → u.regs loop.seed = some (.pred false)) ∧
    (if s.pc = loop.back then 1 else 0) + scratchFuel loop u ≤
      scratchFuel loop s + (if s.pc = scratchParent i then 2 else 0) := by
  let loop := loaderScratchLoop i
  have hB := scratchLoopBounds i
  change (u.pc = loop.back → u.regs loop.seed = some (.pred false)) ∧
    (if s.pc = loop.back then 1 else 0) + scratchFuel loop u ≤
      scratchFuel loop s + (if s.pc = scratchParent i then 2 else 0)
  have hNoEntry {s' : TState} (ho : s'.pc < loop.head ∨ loop.back < s'.pc)
      {ev : Option Event} (hl : 174 ≤ s'.pc) (hh : s'.pc < 1906)
      (ht : WStep kernel Assumptions.all l g s' ev u) : u.pc ≠ loop.back := by
    intro hPc
    have hBack : u.pc = (loaderScratchLoop i).back := hPc
    have hPrevious := stepIntoTail i hl hh hBack ht
    dsimp only [loop] at ho
    rcases ho with h₀ | h₀ <;> rcases hPrevious with h₁ | h₁ <;> omega
  by_cases hBefore : s.pc < loop.head
  · have hTail : s.pc ≠ loop.back := by dsimp only [loop] at hBefore ⊢; omega
    refine ⟨fun ht => (hNoEntry (.inl hBefore) hLo hHi h ht).elim, ?_⟩
    rw [ite_eq_right hTail, Nat.zero_add]
    have hBudget : scratchFuel loop s = 2 := by simp [scratchFuel, hBefore]
    rw [hBudget]
    exact (scratchFuelRange loop u).trans (Nat.le_add_right _ _)
  by_cases hAfter : loop.back < s.pc
  · have hTail : s.pc ≠ loop.back := by omega
    refine ⟨fun ht => (hNoEntry (.inr hAfter) hLo hHi h ht).elim, ?_⟩
    rw [ite_eq_right hTail, Nat.zero_add]
    by_cases hu : u.pc ≤ loop.back
    · have hParent := enclosingBackedge i hLo hHi hAfter hu h
      rw [ite_eq_left hParent]
      exact (scratchFuelRange loop u).trans (Nat.le_add_left _ _)
    · have hab : ¬ u.pc < loop.head := by dsimp only [loop] at hu ⊢; omega
      simp [scratchFuel, hab, hu]
  have hS : loop.head ≤ s.pc ∧ s.pc ≤ loop.back := by omega
  have hL : loop.head ≤ u.pc := scratchCannotLeaveBefore i hS h
  have hBudget : scratchFuel loop s = scratchBudget loop s := by
    simp [scratchFuel, hBefore, hS.2]
  rw [hBudget]
  by_cases hU : u.pc ≤ loop.back
  · have hBudget' : scratchFuel loop u = scratchBudget loop u := by
      simp [scratchFuel, Nat.not_lt.mpr hL, hU]
    rw [hBudget']
    obtain ⟨hNext, hRank⟩ := scratchStep i hS ⟨hL, hU⟩ hSeed h
    exact ⟨hNext, hRank.trans (Nat.le_add_right _ _)⟩
  · refine ⟨fun hPc => (hU hPc.le).elim, ?_⟩
    simp only [scratchFuel, Nat.not_lt.mpr hL, hU, ↓reduceIte, Nat.add_zero]
    have hOne := (scratchBudgetRange loop s).1
    split <;> omega

private theorem visitsAtCons {l : Launch} {g pc : Nat} {s : TState}
    (hs : 174 ≤ s.pc ∧ s.pc < 1906) (e : Option Event) (vs : List Visit) :
    loaderVisitsAt pc (visit kernel l g s e :: vs) =
      loaderVisitsAt pc vs + (if s.pc = pc then 1 else 0) := by
  simp only [loaderVisitsAt, loaderVisits, List.takeWhile_cons, visit_pc]
  split
  · rw [List.countP_cons, visit_pc]
    by_cases h : s.pc = pc <;> simp [h]
  · rename_i h
    exact (h (decide_eq_true hs)).elim

private theorem visitsAtOutside {l : Launch} {g pc : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hout : ¬ (174 ≤ s.pc ∧ s.pc < 1906)) : loaderVisitsAt pc vs = 0 := by
  cases hw <;> simp only [loaderVisitsAt, loaderVisits, List.takeWhile_nil,
    List.takeWhile_cons, visit_pc, List.countP_nil]
  all_goals
    split
    · rename_i hi
      exact (hout (of_decide_eq_true hi)).elim
    · rfl

private theorem visitsAtLast {l : Launch} {g : Nat} {s : TState} {i : Fin 9}
    (hs : 174 ≤ s.pc ∧ s.pc < 1906) (e : Option Event) :
    loaderVisitsAt (loaderScratchLoop i).back [visit kernel l g s e] ≤
      scratchFuel (loaderScratchLoop i) s := by
  let loop := loaderScratchLoop i
  have hB := scratchLoopBounds i
  rw [visitsAtCons hs]
  change 0 + (if s.pc = loop.back then 1 else 0) ≤ scratchFuel loop s
  by_cases hp : s.pc = loop.back
  · have ha : ¬ s.pc < loop.head := by dsimp only [loop] at hp ⊢; omega
    simp only [ite_eq_left hp, Nat.zero_add, scratchFuel, ite_eq_right ha,
      ite_eq_left hp.le]
    exact (scratchBudgetRange loop s).1
  · simp [hp]

private theorem scratchParentRank (i : Fin 9) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : 174 ≤ s.pc ∧ s.pc < 1906)
    (hSeed : s.pc = (loaderScratchLoop i).back →
      s.regs (loaderScratchLoop i).seed = some (.pred false)) :
    loaderVisitsAt (loaderScratchLoop i).back vs ≤
      scratchFuel (loaderScratchLoop i) s + 2 * loaderVisitsAt (scratchParent i) vs := by
  let loop := loaderScratchLoop i
  have extend {t u : TState} {e : Option Event} {rest : List Event} {tail : List Visit}
      (hTail : Walk kernel Assumptions.all l g u rest tail)
      (ht : 174 ≤ t.pc ∧ t.pc < 1906)
      (hClear : t.pc = loop.back → t.regs loop.seed = some (.pred false))
      (hW : WStep kernel Assumptions.all l g t e u)
      (ih : (174 ≤ u.pc ∧ u.pc < 1906) →
        (u.pc = loop.back → u.regs loop.seed = some (.pred false)) →
        loaderVisitsAt loop.back tail ≤
          scratchFuel loop u + 2 * loaderVisitsAt (scratchParent i) tail) :
      loaderVisitsAt loop.back (visit kernel l g t e :: tail) ≤
        scratchFuel loop t + 2 * loaderVisitsAt (scratchParent i) (visit kernel l g t e :: tail) :=
    by
      rw [visitsAtCons ht, visitsAtCons ht]
      obtain ⟨hSeedU, hRank⟩ := scratchParentStep i ht.1 ht.2 hClear hW
      change (if t.pc = loop.back then 1 else 0) + scratchFuel loop u ≤
        scratchFuel loop t + (if t.pc = scratchParent i then 2 else 0) at hRank
      by_cases hU : 174 ≤ u.pc ∧ u.pc < 1906
      · have hh := ih hU hSeedU
        by_cases hP : t.pc = scratchParent i <;> simp only [hP, ↓reduceIte] at hRank ⊢ <;>
          omega
      · rw [visitsAtOutside hTail hU, Nat.zero_add]
        by_cases hP : t.pc = scratchParent i <;> simp only [hP, ↓reduceIte] at hRank ⊢ <;>
          omega
  induction hw with
  | stop => exact Nat.zero_le _
  | tau ht hw ih => exact extend hw hs hSeed (.inl ⟨rfl, ht⟩) ih
  | ev he hw ih => exact extend hw hs hSeed (.inr ⟨_, rfl, he⟩) ih
  | @last s e _ =>
    exact (visitsAtLast (i := i) hs e).trans (Nat.le_add_right _ _)

/-- From the loader entry, each scratch backedge can be visited twice initially and
twice for each visit to its enclosing warm-up or steady ring edge. -/
theorem scratchCountByParent (i : Fin 9) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hStart : s.pc = 174) :
    loaderVisitsAt (loaderScratchLoop i).back vs ≤
      2 * (loaderVisitsAt (scratchParent i) vs + 1) := by
  have hNot : s.pc ≠ (loaderScratchLoop i).back := by
    rw [hStart]
    fin_cases i <;> decide
  have hLocal := scratchParentRank i hw (by rw [hStart]; decide) (fun h => (hNot h).elim)
  have hBudget := scratchFuelRange (loaderScratchLoop i) s
  omega

private def otherCycleSites : List Nat := [287, 401, 1352, 1743, 1847]

private theorem cyclesCovered (pc : Nat) (h : loaderCycleSite pc = true) :
    (otherCycleSites ++ scratchTargets).contains pc = true := by
  change (otherCycleSites ++ [514, 537, 802, 956, 980, 1226, 1426, 1450, 1631]).contains pc = true
  simp [loaderCycleSite, otherCycleSites] at h ⊢
  tauto

private theorem countContains {α : Type} (pcs : List Nat) (xs : List α) (position : α → Nat) :
    xs.countP (fun v => pcs.contains (position v)) ≤
      (pcs.map (fun pc => xs.countP (fun v => position v == pc))).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hSum :
        (pcs.map (fun pc => (a :: xs).countP (fun v => position v == pc))).sum =
          (pcs.map (fun pc => xs.countP (fun v => position v == pc))).sum +
            (pcs.countP fun pc => position a == pc) := by
      clear ih
      induction pcs with
      | nil => rfl
      | cons b bs ih =>
        rw [List.map_cons, List.sum_cons, ih]
        simp only [List.map_cons, List.sum_cons, List.countP_cons]
        omega
    rw [hSum, List.countP_cons]
    by_cases h : pcs.contains (position a) = true
    · have hMem : position a ∈ pcs := List.contains_iff_mem.mp h
      have hOne : 0 < pcs.countP (fun pc => position a == pc) := by
        apply List.countP_pos_iff.mpr
        exact ⟨position a, hMem, beq_self_eq_true _⟩
      rw [ite_eq_left h]
      omega
    · rw [ite_eq_right h, Nat.add_zero]
      omega

private theorem noZeroVisit (vs : List Visit) : loaderVisitsAt 0 vs = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    unfold loaderVisitsAt loaderVisits at ih ⊢
    rw [List.takeWhile_cons]
    split
    · rename_i ht
      have hp : 174 ≤ v.pc ∧ v.pc < 1906 := of_decide_eq_true ht
      have hn : v.pc ≠ 0 := by omega
      rw [List.countP_cons, ih]
      simp [hn]
    · rfl

/-- Only the two scheduler loops, the page-size shift and the two enclosing ring
loops remain in the absolute loader prefix budget. The scratch loops' costs are charged
to their parent ring, with an additional allowance for the first visits. -/
theorem loaderPrefixFromOuterCycles {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hStart : s.pc = 174) (hSub : s.sub = 0) :
    loaderEventCount vs ≤ 5720 * (loaderVisitsAt 287 vs + loaderVisitsAt 401 vs +
      7 * loaderVisitsAt 1352 vs + 7 * loaderVisitsAt 1743 vs + loaderVisitsAt 1847 vs + 19) +
      2 := by
  have hCycle := List.countP_mono_left (l := loaderVisits vs)
    (p := fun v => loaderCycleSite v.pc)
    (q := fun v => (otherCycleSites ++ scratchTargets).contains v.pc)
    (fun v _ h => cyclesCovered v.pc h)
  have hCount := countContains (otherCycleSites ++ scratchTargets) (loaderVisits vs) Visit.pc
  have hTotal := hCycle.trans hCount
  change loaderCycleCount vs ≤ ((otherCycleSites ++ scratchTargets).map
    (fun pc => loaderVisitsAt pc vs)).sum at hTotal
  rw [List.map_append, List.sum_append] at hTotal
  change loaderCycleCount vs ≤
    ([loaderVisitsAt 287 vs, loaderVisitsAt 401 vs, loaderVisitsAt 1352 vs,
      loaderVisitsAt 1743 vs, loaderVisitsAt 1847 vs] : List Nat).sum +
    [loaderVisitsAt 514 vs, loaderVisitsAt 537 vs, loaderVisitsAt 802 vs, loaderVisitsAt 956 vs,
      loaderVisitsAt 980 vs, loaderVisitsAt 1226 vs, loaderVisitsAt 1426 vs,
      loaderVisitsAt 1450 vs, loaderVisitsAt 1631 vs].sum at hTotal
  have h0 := scratchCountByParent 0 hw hStart
  have h1 := scratchCountByParent 1 hw hStart
  have h2 := scratchCountByParent 2 hw hStart
  have h3 := scratchCountByParent 3 hw hStart
  have h4 := scratchCountByParent 4 hw hStart
  have h5 := scratchCountByParent 5 hw hStart
  have h6 := scratchCountByParent 6 hw hStart
  have h7 := scratchCountByParent 7 hw hStart
  have h8 := scratchCountByParent 8 hw hStart
  change loaderVisitsAt 514 vs ≤ 2 * (loaderVisitsAt 0 vs + 1) at h0
  change loaderVisitsAt 537 vs ≤ 2 * (loaderVisitsAt 0 vs + 1) at h1
  change loaderVisitsAt 802 vs ≤ 2 * (loaderVisitsAt 0 vs + 1) at h2
  change loaderVisitsAt 956 vs ≤ 2 * (loaderVisitsAt 1352 vs + 1) at h3
  change loaderVisitsAt 980 vs ≤ 2 * (loaderVisitsAt 1352 vs + 1) at h4
  change loaderVisitsAt 1226 vs ≤ 2 * (loaderVisitsAt 1352 vs + 1) at h5
  change loaderVisitsAt 1426 vs ≤ 2 * (loaderVisitsAt 1743 vs + 1) at h6
  change loaderVisitsAt 1450 vs ≤ 2 * (loaderVisitsAt 1743 vs + 1) at h7
  change loaderVisitsAt 1631 vs ≤ 2 * (loaderVisitsAt 1743 vs + 1) at h8
  have hZero := noZeroVisit vs
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hTotal
  exact (loaderPrefixFromCycles hw (by omega) (by omega) hSub).trans (by omega)

end
end PTX.Kernels.TmlFa4Fwd.Loader
