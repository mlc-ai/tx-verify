-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRingPrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderScratchParent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private theorem ringNoReentry (j : Fin 2) :
    let site := ringCounterSite j
    loaderBackEdges.all (fun (pc, target) =>
      (!(site.head ≤ pc) || site.head ≤ target) &&
        (!(site.branch < pc) || site.branch < target)) = true := by
  fin_cases j <;> decide

private theorem ringReverse {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hl : 174 ≤ s.pc) (hh : s.pc < 1906) (hRev : u.pc < s.pc)
    (hw : WStep kernel Assumptions.all l g s e u) : (s.pc, u.pc) ∈ loaderBackEdges := by
  rcases hw with ⟨-, ht⟩ | ⟨ev, -, he⟩
  · exact loaderTauBackEdge hl hh hRev.le ht
  · have he' : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tmpl, ht, hf⟩ := he
      exact ⟨tmpl, by rwa [← loaderOutCore hl hh], hf⟩
    rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with hc | hc <;> omega

private theorem ringProgress (j : Fin 2) {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hl : 174 ≤ s.pc) (hh : s.pc < 1906) (hw : WStep kernel Assumptions.all l g s e u) :
    let site := ringCounterSite j
    (site.head ≤ s.pc → site.head ≤ u.pc) ∧ (site.branch < s.pc → site.branch < u.pc) := by
  let site := ringCounterSite j
  change (site.head ≤ s.pc → site.head ≤ u.pc) ∧ (site.branch < s.pc → site.branch < u.pc)
  by_cases hf : s.pc ≤ u.pc
  · exact ⟨fun h => h.trans hf, fun h => h.trans_le hf⟩
  have hm := ringReverse hl hh (by omega) hw
  have hc := List.all_eq_true.mp (ringNoReentry j) _ hm
  change ((!(site.head ≤ s.pc) || site.head ≤ u.pc) &&
    (!(site.branch < s.pc) || site.branch < u.pc)) = true at hc
  constructor
  · intro h
    simpa [h] using (Bool.and_eq_true_iff.mp hc).1
  · intro h
    simpa [h] using (Bool.and_eq_true_iff.mp hc).2

private theorem ringPcs (j : Fin 2) :
    let site := ringCounterSite j
    174 ≤ site.head ∧ site.head < site.branch ∧ site.branch < 1906 := by
  fin_cases j <;> decide

theorem noLaterRingBranchVisits (j : Fin 2) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : (ringCounterSite j).branch < s.pc) :
    loaderVisitsAt (ringCounterSite j).branch vs = 0 := by
  let site := ringCounterSite j
  have hB : 174 ≤ site.head ∧ site.head < site.branch ∧ site.branch < 1906 := ringPcs j
  have step {t : TState} (h : site.branch < t.pc) (e : Option Event) (tail : List Visit)
      (ih : t.pc < 1906 → loaderVisitsAt site.branch tail = 0) :
      loaderVisitsAt site.branch (visit kernel l g t e :: tail) = 0 := by
    unfold loaderVisitsAt loaderVisits
    rw [List.takeWhile_cons, visit_pc]
    split
    · rename_i ht
      have hh : (174 ≤ t.pc ∧ t.pc < 1906) := of_decide_eq_true ht
      rw [List.countP_cons, visit_pc]
      have hne : t.pc ≠ site.branch := by omega
      simpa [loaderVisitsAt, loaderVisits, hne] using ih hh.2
    · rfl
  induction hw with
  | stop => rfl
  | @tau t u es vs ht hh ih =>
    exact step hp none _ (fun hh =>
      ih ((ringProgress j (by change site.branch < t.pc at hp; omega) hh
        (.inl ⟨rfl, ht⟩)).2 hp))
  | @ev t u e es vs he hh ih =>
    exact step hp (some e) _ (fun hh =>
      ih ((ringProgress j (by change site.branch < t.pc at hp; omega) hh
        (.inr ⟨e, rfl, he⟩)).2 hp))
  | last => exact step hp (some _) [] (fun _ => rfl)

private theorem localRingBeyond (j : Fin 2) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : (ringCounterSite j).branch < s.pc) : ringBranchVisits j vs = 0 := by
  cases hw <;> simp only [ringBranchVisits, List.takeWhile_nil, List.countP_nil,
    List.takeWhile_cons, visit_pc]
  all_goals
    split
    · rename_i h
      exact (Nat.not_le.mpr hp (of_decide_eq_true h).2).elim
    · rfl

private theorem sameRingStepCount (j : Fin 2) {l : Launch} {g : Nat} {s : TState}
    {tail : List Visit} (h : (ringCounterSite j).head ≤ s.pc ∧ s.pc ≤ (ringCounterSite j).branch)
    (e : Option Event) (hCount : loaderVisitsAt (ringCounterSite j).branch tail =
      ringBranchVisits j tail) :
    loaderVisitsAt (ringCounterSite j).branch (visit kernel l g s e :: tail) =
      ringBranchVisits j (visit kernel l g s e :: tail) := by
  have hB := ringPcs j
  unfold loaderVisitsAt loaderVisits at hCount ⊢
  unfold ringBranchVisits at hCount ⊢
  dsimp only at hCount ⊢
  simp only [List.takeWhile_cons, visit_pc]
  split <;> split
  · rw [List.countP_cons, List.countP_cons, hCount]
  · rename_i bad
    exact (bad (decide_eq_true h)).elim
  · rename_i bad good
    exact (bad (decide_eq_true ⟨by omega, by omega⟩)).elim
  · rename_i bad _
    exact (bad (decide_eq_true ⟨by omega, by omega⟩)).elim

/-- Once a ring has begun, its local branch count is also its count in the rest of
the loader role. The audited backedges cannot return to a finished ring. -/
theorem ringVisitCountWithinRole (j : Fin 2) {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : (ringCounterSite j).head ≤ s.pc) :
    loaderVisitsAt (ringCounterSite j).branch vs = ringBranchVisits j vs := by
  let site := ringCounterSite j
  have hB : 174 ≤ site.head ∧ site.head < site.branch ∧ site.branch < 1906 := ringPcs j
  have extend {t u : TState} {e : Option Event} {es : List Event} {tail : List Visit}
      (h : site.head ≤ t.pc) (hStep : WStep kernel Assumptions.all l g t e u)
      (hW : Walk kernel Assumptions.all l g t (e.toList ++ es) (visit kernel l g t e :: tail))
      (ih : site.head ≤ u.pc → loaderVisitsAt site.branch tail = ringBranchVisits j tail) :
      loaderVisitsAt site.branch (visit kernel l g t e :: tail) =
        ringBranchVisits j (visit kernel l g t e :: tail) := by
    by_cases ht : site.branch < t.pc
    · exact (noLaterRingBranchVisits j hW ht).trans (localRingBeyond j hW ht).symm
    have hLive : t.pc ≤ site.branch := by omega
    exact sameRingStepCount j ⟨h, hLive⟩ e (ih
      ((ringProgress j (by omega) (by omega) hStep).1 h))
  induction hw with
  | stop => rfl
  | tau ht hw ih => exact extend hp (.inl ⟨rfl, ht⟩) (.tau ht hw) ih
  | ev he hw ih => exact extend hp (.inr ⟨_, rfl, he⟩) (.ev he hw) ih
  | @last s e he =>
    by_cases h : site.branch < s.pc
    · exact (noLaterRingBranchVisits j (.last he) h).trans (localRingBeyond j (.last he) h).symm
    · exact sameRingStepCount j ⟨hp, by change s.pc ≤ site.branch; omega⟩ (some e) rfl

private def ringEntryTarget (site : RingCounterSite) : Op → Bool
  | .bra target _ => target ≤ site.head || site.branch < target
  | .brx .. => false
  | _ => true

private theorem ringEntryCode (j : Fin 2) :
    let site := ringCounterSite j
    ((kernel.code.drop 174).take (site.head - 174)).all
      (fun i => ringEntryTarget site i.op) = true := by
  fin_cases j <;> set_option maxRecDepth 100000 in decide +kernel

private theorem entryTargetFacts {site : RingCounterSite} {op : Op} {pc : Nat}
    (h : ringEntryTarget site op = true) :
    (∀ p, ¬ BrxTarget op p) ∧
      (nextPc op pc = pc + 1 ∨ nextPc op pc ≤ site.head ∨ site.branch < nextPc op pc) := by
  cases op <;> simp only [ringEntryTarget, Bool.false_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at h
  case bra target uni => exact ⟨by simp [BrxTarget], .inr h⟩
  all_goals exact ⟨by simp [BrxTarget], .inl rfl⟩

private theorem ringEntryStep (j : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : 174 ≤ s.pc) (hHi : s.pc < (ringCounterSite j).head)
    (hw : WStep kernel Assumptions.all l g s e u) :
    u.pc ≤ (ringCounterSite j).head ∨ (ringCounterSite j).branch < u.pc := by
  let site := ringCounterSite j
  have hB : 174 ≤ site.head ∧ site.head < site.branch ∧ site.branch < 1906 := ringPcs j
  have hs : s.pc < site.head := hHi
  have hh : s.pc < 1906 := by omega
  change u.pc ≤ site.head ∨ site.branch < u.pc
  rcases hw with ⟨-, ht⟩ | ⟨ev, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo hh]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    have hGet : ((kernel.code.drop 174).take (site.head - 174))[s.pc - 174]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    have hCode := List.all_eq_true.mp (ringEntryCode j) ins (List.mem_of_getElem? hGet)
    obtain ⟨hBrx, hTargets⟩ := entryTargetFacts (pc := s.pc) hCode
    rcases tau_core_frame hc ht' with rfl | hF
    · left
      change s.pc + 1 ≤ site.head
      omega
    · rw [hF.pc.resolve_right (hBrx _)]
      rcases hTargets with hPc | hPc
      · rw [hPc]
        omega
      · exact hPc
  · have he' : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tmpl, ht, hf⟩ := he
      exact ⟨tmpl, by rwa [← loaderOutCore hLo hh], hf⟩
    rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with hp | hp <;> omega

private theorem ringHeadCountStep (j : Fin 2) {l : Launch} {g : Nat} {s : TState}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < (ringCounterSite j).head)
    (e : Option Event) (tail : List Visit) :
    loaderVisitsAt (ringCounterSite j).branch (visit kernel l g s e :: tail) =
      loaderVisitsAt (ringCounterSite j).branch tail := by
  have hB := ringPcs j
  unfold loaderVisitsAt loaderVisits
  rw [List.takeWhile_cons, visit_pc]
  split
  · rw [List.countP_cons, visit_pc]
    have hNe : s.pc ≠ (ringCounterSite j).branch := by omega
    simp [hNe]
  · rename_i h
    exact (h (decide_eq_true ⟨hLo, by omega⟩)).elim

private theorem belowLoaderNoCount {l : Launch} {g pc : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs) (hs : s.pc < 174) :
    loaderVisitsAt pc vs = 0 := by
  cases hw <;> simp only [loaderVisitsAt, loaderVisits, List.takeWhile_nil, List.countP_nil,
    List.takeWhile_cons, visit_pc]
  all_goals
    split
    · rename_i h
      have hc : 174 ≤ s.pc ∧ s.pc < 1906 := of_decide_eq_true h
      omega
    · rfl

/-- A loader prefix before a ring either has no visit to its branch, or reaches the
decoded entry and can be cut there. The caller may carry any invariant preserved
by the actual steps before entry. -/
theorem locateLoaderRing (j : Fin 2) {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {P : TState → Prop} (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : 174 ≤ s.pc ∧ s.pc ≤ (ringCounterSite j).head) (hP : P s)
    (step : ∀ {t u : TState} {e : Option Event},
      174 ≤ t.pc → t.pc < (ringCounterSite j).head →
      WStep kernel Assumptions.all l g t e u → P t → P u) :
    loaderVisitsAt (ringCounterSite j).branch vs = 0 ∨
      ∃ u rest tail, u.pc = (ringCounterSite j).head ∧ P u ∧
        loaderVisitsAt (ringCounterSite j).branch vs =
          loaderVisitsAt (ringCounterSite j).branch tail ∧
        Walk kernel Assumptions.all l g u rest tail := by
  let site := ringCounterSite j
  have hB : 174 ≤ site.head ∧ site.head < site.branch ∧ site.branch < 1906 := ringPcs j
  have advance {t u : TState} {e : Option Event} {rest : List Event} {tail : List Visit}
      (hP : P t) (hT : 174 ≤ t.pc ∧ t.pc ≤ site.head)
      (hStep : WStep kernel Assumptions.all l g t e u)
      (hW : Walk kernel Assumptions.all l g u rest tail)
      (hStart : Walk kernel Assumptions.all l g t (e.toList ++ rest)
        (visit kernel l g t e :: tail))
      (ih : (174 ≤ u.pc ∧ u.pc ≤ site.head) → P u →
        loaderVisitsAt site.branch tail = 0 ∨ ∃ v after suffix, v.pc = site.head ∧ P v ∧
          loaderVisitsAt site.branch tail = loaderVisitsAt site.branch suffix ∧
          Walk kernel Assumptions.all l g v after suffix) :
      loaderVisitsAt site.branch (visit kernel l g t e :: tail) = 0 ∨
        ∃ v after suffix, v.pc = site.head ∧ P v ∧
          loaderVisitsAt site.branch (visit kernel l g t e :: tail) =
            loaderVisitsAt site.branch suffix ∧ Walk kernel Assumptions.all l g v after suffix := by
    by_cases he : t.pc = site.head
    · exact .inr ⟨t, _, _, he, hP, rfl, hStart⟩
    have hlt : t.pc < site.head := by omega
    rw [ringHeadCountStep j hT.1 hlt]
    rcases ringEntryStep j hT.1 hlt hStep with hU | hPast
    · by_cases hlo : 174 ≤ u.pc
      · exact ih ⟨hlo, hU⟩ (step hT.1 hlt hStep hP)
      · exact .inl (belowLoaderNoCount hW (by omega))
    · exact .inl (noLaterRingBranchVisits j hW hPast)
  induction hw with
  | stop => exact .inl rfl
  | tau ht hh ih => exact advance hP hs (.inl ⟨rfl, ht⟩) hh (.tau ht hh) ih
  | ev he hh ih => exact advance hP hs (.inr ⟨_, rfl, he⟩) hh (.ev he hh) ih
  | @last s e he =>
    by_cases hpc : s.pc = site.head
    · exact .inr ⟨s, _, _, hpc, hP, rfl, .last he⟩
    have hl : s.pc ≤ site.head := hs.2
    have hlt : s.pc < site.head := by omega
    rw [ringHeadCountStep j hs.1 hlt]
    exact .inl rfl

/-- An entry invariant for the selected ring bounds its branch count throughout a
loader walk, including traces that skip the ring or suspend before reaching it. -/
theorem loaderRingPrefixWithEntry (j : Fin 2) {l : Launch} {g budget : Nat}
    {s : TState} {es : List Event} {vs : List Visit} {P : TState → Prop}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : 174 ≤ s.pc ∧ s.pc ≤ (ringCounterSite j).head) (hP : P s)
    (step : ∀ {t u : TState} {e : Option Event},
      174 ≤ t.pc → t.pc < (ringCounterSite j).head →
      WStep kernel Assumptions.all l g t e u → P t → P u)
    (entry : ∀ t, t.pc = (ringCounterSite j).head → P t →
      ∃ k trips, trips < 2 ^ 31 ∧ k < counterLimit j trips ∧
        counterLimit j trips - k ≤ budget ∧ At t (ringCounterSite j).head
          [((ringCounterSite j).counter, b32 k), (1091, b32 trips)]) :
    loaderVisitsAt (ringCounterSite j).branch vs ≤ 5 * (budget + 1) := by
  rcases locateLoaderRing j hw hs hP step with hZero | ⟨t, rest, tail, hp, hT, hCount, hWalk⟩
  · simp [hZero]
  · obtain ⟨k, trips, hTrips, hk, hb, ht⟩ := entry t hp hT
    rw [hCount, ringVisitCountWithinRole j hWalk hp.ge]
    exact (ringVisitsFromEntry j hWalk hTrips hk ht).trans (by omega)

theorem loaderVisitsAt_le_length (pc : Nat) (visits : List Visit) :
    loaderVisitsAt pc visits ≤ visits.length := by
  apply (List.countP_le_length (p := _)).trans
  unfold loaderVisits
  induction visits with
  | nil => rfl
  | cons v vs ih =>
    rw [List.takeWhile_cons]
    split
    · exact Nat.succ_le_succ ih
    · exact Nat.zero_le _

theorem loaderVisitsAt_le_append (pc : Nat) (pre tail : List Visit) :
    loaderVisitsAt pc (pre ++ tail) ≤ pre.length + loaderVisitsAt pc tail := by
  induction pre with
  | nil => simp
  | cons v pre ih =>
    unfold loaderVisitsAt loaderVisits at ih ⊢
    simp only [List.cons_append, List.takeWhile_cons, List.length_cons]
    split
    · rw [List.countP_cons]
      split <;> omega
    · exact Nat.zero_le _

end
end PTX.Kernels.TmlFa4Fwd.Loader
