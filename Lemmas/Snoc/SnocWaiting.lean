-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocOrder
public import Lemmas.Execution.NoAsync

@[expose] public section

namespace PTX
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event}
  {r : Nat → Option AsyncCopy.Ref}

/-- Checked histories keep both endpoints of a resource dependency in the prefix. -/
theorem ctaWaits_snoc_old (hc : CtaBarHistoryOk L X) {i j : EvId} {b b' : Bool}
    (h : CtaBarWaits L (X.snoc g e r) i j b b') : CtaBarWaits L X i j b b' := by
  have hr := h.2.2
  change (b = false ∧ b' = false ∧ _) ∨ (b = false ∧ b' = true ∧ _) ∨
    (b = false ∧ b' = true ∧ _) at hr
  have src : (∃ev, X.get i = some ev) ∧ (∃ev, X.get j = some ev) := by
    rcases hr with ⟨_,_,c,a,b,ra,rb,ha,hb,_,he,hf⟩ | ⟨_,_,_,key,hi,hj⟩ |
      ⟨_,_,key,a,ra,hj,ha,he,_⟩
    · exact ⟨hc.ref_present (List.mem_of_getElem? ha) he,
        hc.ref_present (List.mem_of_getElem? hb) hf⟩
    · exact ⟨hc.generation_present hi.2.2,hc.generation_present hj.2.2⟩
    · exact ⟨hc.ref_present (List.mem_of_getElem? ha) he,hc.generation_present hj.2.2⟩
  refine ⟨src.1,src.2,?_⟩
  simp only [snoc_ctaBarK_history hc, snoc_ctaBarArrivalK_history hc] at hr
  exact hr

theorem clusterWaits_snoc_old (hc : ClusterHistoryOk L X) {i j : EvId} {b b' : Bool}
    (h : ClusterWaits L (X.snoc g e r) i j b b') : ClusterWaits L X i j b b' := by
  have hr := h.2.2
  have src : (∃ev, X.get i = some ev) ∧ (∃ev, X.get j = some ev) := by
    rcases hr with ⟨c,a,b,ra,rb,ha,hb,_,he,hf,_⟩ | ⟨_,_,c,ra,ha,he,hf⟩ |
      ⟨_,_,phase,c,ha,hb⟩ | ⟨_,_,phase,c,ha,hb⟩
    · exact ⟨hc.ref_present (List.mem_of_getElem? ha) he,
        hc.ref_present (List.mem_of_getElem? hb) hf⟩
    · exact ⟨hc.ref_present ha he,hc.ref_present ha hf⟩
    all_goals
      obtain ⟨pc,aligned,hp⟩ := hc.arrival_present ha
      exact ⟨⟨_,hp⟩,hc.wait_present hb⟩
  exact ⟨src.1,src.2,hr⟩

theorem Execution.NoTma.emptyHistory (hn : X.NoTma) (hh : Tmem.Pair.HistoriesOk L X)
    (cta : Nat) : X.tmemHistory cta = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro record hr
  cases hn _ _ _ (((hh.1 cta).1 record hr).2.2.2.2.1 (0 : Fin 32))

theorem Execution.NoTma.emptyPairing (hn : X.NoTma) (hh : Tmem.Pair.HistoriesOk L X) :
    X.tmemPairing = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q hq
  cases hn _ _ _ ((hh.2.1 q hq).1.2.1.2.2.1 (0 : Fin 32))

end
end
end PTX
