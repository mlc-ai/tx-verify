-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpOpen
public import Lemmas.Step.WarpAcyclic
public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Snoc.Collectives

@[expose] public section

/-! # A lane collective appended to all its lanes at once

A proof tool. Let every thread of `ds` be able to perform a lane-collective event `ev h`
(`Kind.LaneColl`: a warp collective or a ballot) after τ-steps of its run, with its last event
released and its cluster launched if it has not started. Appending all of them is a consistent
counted extension (`appendLanes_counted_extension_lane`), provided no new event matches an old
one in a collective instance (`WarpMatch`), every new event is ready (DEP-ORDER: its instance has
an event in every lane of its mask, which only the whole instance can meet) and the extension
satisfies the collective rules (DEP-WARP-SHUFFLE, DEP-WARP-ELECT, DEP-WARP-BARRIER, DEP-WARP-VOTE).
The lanes are appended one by one, keeping `WarpOpen` and the visibility into old events; the
readiness, the collective rules and the waiting graph are checked on the result. Old events keep
their readiness (`appendLanes_ready_old`). For a warp collective other than the ballot the ballot
and lane-value rules are inherited (`appendLanes_counted_extension`). -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {ds : List Nat} {ev : Nat → Event}

/-- A thread outside `ds` that has started, or whose cluster has been launched, still has. -/
theorem started_appendLanes_lane (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) {h : Nat} (hh : h ∉ ds)
    (hst : X.tr h ≠ [] ∨ Launched L X h) :
    (X.appendLanes ds ev).tr h ≠ [] ∨ Launched L (X.appendLanes ds ev) h := by
  rw [appendLanes_tr_of_not_mem hh]
  refine hst.imp id (fun hl ⟨i, s, ts, pc, hi⟩ => hl ⟨i, s, ts, pc, ?_⟩)
  exact (appendLanes_get_kind (fun h' hm => (hw h' hm).ne id)).mp hi

/-- **An old event that `X` holds ready stays ready** after the lane collectives are appended: the
new events are no matrix events, so an exit keeps its matrix count (`ThreadAppend.need_of_old`). -/
theorem appendLanes_ready_old (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) {j : EvId}
    (hj : j.2 < (X.tr j.1).length) (hr : Ready L X j) : Ready L (X.appendLanes ds ev) j := by
  have ha := appendLanes_threadAppend (X := X) (ds := ds) (ev := ev)
  have hpres : ∀ i p, X.AsyncPresent i p → (X.appendLanes ds ev).AsyncPresent i p :=
    fun _ _ => (appendLanes_asyncPresent_lane hd hw).mpr
  have hex : (∃ pc op own recv, X.get j = some ⟨pc, .matrix op own recv⟩) →
      ∀ v pc, X.get v = some ⟨pc, .exit⟩ →
      ((X.appendLanes ds ev).tr v.1).countP isMatrix ≤ (X.tr v.1).countP isMatrix := by
    intro _ v _ _
    rw [appendLanes_tr]
    split_ifs with hv
    · have hm : isMatrix (ev v.1) = false := by
        have := hw v.1 hv
        generalize ev v.1 = q at this ⊢
        obtain ⟨pc, k⟩ := q
        cases k <;> first | exact (this : False).elim | rfl
      simp [hm]
    · exact le_refl _
  intro n hn
  rcases ha.need_of_old hex (ha.not_new hj) hn with ⟨x, hx, fills, rfl, hf⟩ | ⟨n', hn', himp⟩
  · exact ⟨x, hx, hf⟩
  · have h' := hr n' hn'
    cases n' <;> cases n <;> simp only [NeedImp] at himp
    · obtain ⟨x, hx, hf⟩ := h'
      exact ⟨x, ha.present_mono hpres hx, himp x hx hf⟩
    · exact himp h'

/-- **Readiness after appending the lane collectives** (DEP-ORDER): old events keep their
readiness, the previous last event of each lane is ready (`Released`), and the new events are
ready by hypothesis. -/
theorem appendLanes_ready (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) (hrel : ∀ h ∈ ds, Released L X h)
    (hnew : ∀ h ∈ ds, Ready L (X.appendLanes ds ev) (h, (X.tr h).length)) :
    ∀ j, Returned (X.appendLanes ds ev) j → Ready L (X.appendLanes ds ev) j := by
  intro j hr
  by_cases hjn : j.1 ∈ ds ∧ j.2 = (X.tr j.1).length
  · obtain ⟨j1, j2⟩ := j
    obtain ⟨h1, h2⟩ := hjn
    simp only at h1 h2
    subst h2
    exact hnew j1 h1
  have hjo : (X.appendLanes ds ev).get j = X.get j := by
    rw [appendLanes_get, ite_eq_right hjn]
  refine appendLanes_ready_old hd hw ?_ ?_
  · unfold Returned at hr
    rw [hjo] at hr
    cases hget : X.get j with
    | none => simp [hget] at hr
    | some q => exact len_of_get hget
  by_cases hrX : Returned X j
  · exact hX.dependency.ready j hrX
  unfold Returned at hr hrX
  rw [hjo] at hr
  cases hget : X.get j with
  | none => simp [hget] at hr
  | some q =>
  obtain ⟨pc, k⟩ := q
  simp only [hget] at hr hrX
  have hjold : j.2 < (X.tr j.1).length := len_of_get hget
  have finish : j.2 + 1 < ((X.appendLanes ds ev).tr j.1).length →
      ¬ j.2 + 1 < (X.tr j.1).length → k.resume = .blocking false → Ready L X j := by
    intro h1 h2 hres
    rw [appendLanes_len] at h1
    split_ifs at h1 with hjg
    · obtain ⟨j1, j2⟩ := j
      simp only at hjg h1 h2 hjold hget
      have hj2 : j2 = (X.tr j1).length - 1 := by omega
      subst hj2
      exact (hrel j1 hjg).ready pc k hget hres
    · exact absurd h1 h2
  split at hr
  · rename_i heq
    cases heq
    simp only at hrX
    exact absurd hr hrX
  · rename_i ev' hnw heq
    cases heq
    split at hrX
    · rename_i heq'
      cases heq'
      exact absurd rfl (hnw _ _ _ _ _ _)
    · rename_i heq'
      cases heq'
      cases hres : k.resume with
      | blocking c =>
        cases c
        · simp only [hres] at hr hrX
          exact finish hr hrX hres
        · simp only [hres] at hrX
          exact absurd trivial hrX
      | _ => simp only [hres] at hr
    · rename_i heq'
      cases heq'
  · exact hr.elim

/-- What the lane-by-lane appends keep: the open obligations and the visibility into every old
event. -/
private theorem appendLanes_open_lane (hX : Consistent L K A mem0 X) {ds' : List Nat}
    (hsub : ∀ h ∈ ds', h ∈ ds) (hd : ds'.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    (hst : ∀ h ∈ ds, X.tr h ≠ [] ∨ Launched L X h)
    (hfresh : ∀ h ∈ ds, ∀ j : EvId, j.2 < (X.tr j.1).length →
      ¬ WarpMatch L (X.appendLanes ds ev) (h, (X.tr h).length) j) :
    WarpOpen L A (X.appendLanes ds' ev) ∧
      (∀ l v f, X.RefPresent f →
          (modelCausality L (X.appendLanes ds' ev) l v f ↔ modelCausality L X l v f)) ∧
      ∀ x f, f.2 < (X.tr f.1).length →
          (baseCausality L (X.appendLanes ds' ev) x f ↔ baseCausality L X x f) := by
  induction ds' with
  | nil => rw [appendLanes_nil]; exact ⟨hX.warpOpen, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  | cons h ds' ih =>
    have hh : h ∈ ds := hsub h List.mem_cons_self
    have hn := (List.nodup_cons.mp hd).1
    obtain ⟨hO, hV, hH⟩ := ih (fun h' hm => hsub h' (List.mem_cons_of_mem _ hm))
      (List.nodup_cons.mp hd).2
    have hw' : ∀ h' ∈ ds', (ev h').kind.LaneColl :=
      fun h' hm => hw h' (hsub h' (List.mem_cons_of_mem _ hm))
    have hfr : FreshWarpBar L (X.appendLanes ds' ev) h (ev h) := by
      intro mask inst he j pc hj hq hs
      have hjo : j.2 < (X.tr j.1).length := by
        have := appendLanes_len (X := X) (ds := ds') (ev := ev) j.1
        split_ifs at this <;> omega
      rw [appendLanes_get_old hjo] at hq
      apply hfresh h hh j hjo
      refine .inr (.inl ⟨mask, inst, ⟨(ev h).pc, ?_⟩, ⟨pc, Execution.le_get le_appendLanes hq⟩⟩)
      rw [appendLanes_get_new hh, ← he]
    have hbo : ∀ {x f : EvId}, f.2 < ((X.appendLanes ds' ev).tr f.1).length →
        (baseCausality L ((X.appendLanes ds' ev).snoc h (ev h) (fun _ => none)) x f ↔
          baseCausality L (X.appendLanes ds' ev) x f) :=
      fun hf => baseCausality_snoc_old_lane hO.clusterHistory (hw h hh) hfr hf
    rw [appendLanes_cons hn]
    have hold : ∀ {f : EvId}, f.2 < (X.tr f.1).length →
        f.2 < ((X.appendLanes ds' ev).tr f.1).length := fun {f} hf =>
      lt_of_lt_of_le hf ((le_appendLanes (X := X) (ds := ds') (ev := ev)).1 f.1).length_le
    refine ⟨hO.snoc_lane (hw h hh) (started_appendLanes_lane hw' hn (hst h hh)) hfr,
      fun l v f hf => ?_, fun x f hf => (hbo (hold hf)).trans (hH x f hf)⟩
    rw [← hV l v f hf]
    apply (hw h hh).asyncSilent.modelCausality_snoc_old hbo
      (snoc_allocResultBefore_old_of_not_write (fun _ _ he => (hw h hh).ne id he))
    have := refPresent_issuer_lt hX.effectValidity hf
    have := (le_appendLanes (X := X) (ds := ds') (ev := ev)).1 f.issuer.1
    exact lt_of_lt_of_le ‹_› this.length_le

/-- **A lane collective appended to all its lanes is consistent**, given the readiness of the new
events and the collective rules on the result. -/
theorem appendLanes_consistent_lane (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hlt : ∀ h ∈ ds, h < L.threads) (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    (hst : ∀ h ∈ ds, X.tr h ≠ [] ∨ Launched L X h) (hrel : ∀ h ∈ ds, Released L X h)
    (hrun : ∀ h ∈ ds, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧ EStep K A L h t1 (ev h) o)
    (hfresh : ∀ h ∈ ds, ∀ j : EvId, j.2 < (X.tr j.1).length →
      ¬ WarpMatch L (X.appendLanes ds ev) (h, (X.tr h).length) j)
    (hnew : ∀ h ∈ ds, Ready L (X.appendLanes ds ev) (h, (X.tr h).length))
    (hshfl : ShflOk L (X.appendLanes ds ev)) (helect : ElectOk L (X.appendLanes ds ev))
    (hwarp : WarpBarOk L (X.appendLanes ds ev)) (hvote : VoteOk L (X.appendLanes ds ev))
    (hvalue : WarpValueOk L (X.appendLanes ds ev))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev)) :
    Consistent L K A mem0 (X.appendLanes ds ev) := by
  have le : X.le (X.appendLanes ds ev) := le_appendLanes
  obtain ⟨hO, hV, hH⟩ := appendLanes_open_lane hX (fun h hm => hm) hd hw hst hfresh
  have hreads {v a bs} : (X.appendLanes ds ev).MemReads v a bs ↔ X.MemReads v a bs :=
    appendLanes_memReads_lane hd hw
  have hwrites {v a bs} : (X.appendLanes ds ev).MemWrites v a bs ↔ X.MemWrites v a bs :=
    appendLanes_memWrites_lane hd hw
  apply consistent_preserving_extension hX le_appendLanes
  · intro h hh
    rw [appendLanes_tr]
    split_ifs with hm
    · obtain ⟨t, t1, o, hr, hl, he⟩ := hrun h hm
      exact ⟨o, hr.snoc hl he⟩
    · exact hX.thr h hh
  · intro h hh
    rw [appendLanes_tr, ite_eq_right (fun hm => by have := hlt h hm; omega)]
    exact hX.outside h hh
  · exact fun v a bs h => hreads.mp h
  · exact fun v a bs h => hwrites.mp h
  · exact fun v a bs h => hwrites.mpr h
  · exact fun v a bs h k => le.2.1 v k ⟨a, bs, hreads.mp h⟩
  · exact hV
  · exact appendLanes_ready hX hd hw hrel hnew
  · exact hshfl
  · exact (appendLanes_sinkFrame_lane hX hd hw hfresh hO.effectValidity hO.clusterHistory
      (fun x f hf => (hH x f hf).mp)).orderOk hX.orderOk
  · exact hasm
  · exact hO.tma
  · rfl
  · exact
      { ctaBar := hO.ctaBar, cluster := hO.clusterHistory, elect := helect, vote := hvote,
        warpValue := hvalue, warpBar := hwarp, matrix := hO.matrix, clc := hO.clc,
        tensor := hO.tensor, store := hO.store, atomic := hO.atomic, fenceSc := hO.fenceSc,
        tmemPair := hO.tmemPair, tmemPairResult := hO.tmemPairResult,
        tmemPairCompletion :=
          Tmem.Pair.completionClosed_of_growth le rfl rfl hX.tmemPair hX.tmemPairCompletion,
        tcCommit := hO.tcCommit,
        mmaCompletion := TcMma.completionClosed_of_growth le rfl hX.tma.2.1 hX.mmaCompletion,
        tcRead := hO.tcRead, reduce := hO.reduce }

/-- **A lane collective appended to all its lanes is a counted extension.** -/
theorem appendLanes_counted_extension_lane (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hds : ds ≠ []) (hlt : ∀ h ∈ ds, h < L.threads) (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    (hst : ∀ h ∈ ds, X.tr h ≠ [] ∨ Launched L X h) (hrel : ∀ h ∈ ds, Released L X h)
    (hrun : ∀ h ∈ ds, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧ EStep K A L h t1 (ev h) o)
    (hfresh : ∀ h ∈ ds, ∀ j : EvId, j.2 < (X.tr j.1).length →
      ¬ WarpMatch L (X.appendLanes ds ev) (h, (X.tr h).length) j)
    (hnew : ∀ h ∈ ds, Ready L (X.appendLanes ds ev) (h, (X.tr h).length))
    (hshfl : ShflOk L (X.appendLanes ds ev)) (helect : ElectOk L (X.appendLanes ds ev))
    (hwarp : WarpBarOk L (X.appendLanes ds ev)) (hvote : VoteOk L (X.appendLanes ds ev))
    (hvalue : WarpValueOk L (X.appendLanes ds ev))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  refine ⟨_, appendLanes_consistent_lane hX hd hlt hw hst hrel hrun hfresh hnew hshfl helect hwarp
    hvote hvalue hasm, le_appendLanes, ?_⟩
  rw [size_appendLanes hX hd hlt (fun h hh => Kind.LaneColl.counts (hw h hh))]
  have := List.length_pos_of_ne_nil hds
  omega

/-- **A warp collective other than the ballot appended to all its lanes is a counted
extension**: the ballot and lane-value rules are those of `X`. -/
theorem appendLanes_counted_extension (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hds : ds ≠ []) (hlt : ∀ h ∈ ds, h < L.threads) (hw : ∀ h ∈ ds, (ev h).kind.WarpColl)
    (hst : ∀ h ∈ ds, X.tr h ≠ [] ∨ Launched L X h) (hrel : ∀ h ∈ ds, Released L X h)
    (hrun : ∀ h ∈ ds, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧ EStep K A L h t1 (ev h) o)
    (hfresh : ∀ h ∈ ds, ∀ j : EvId, j.2 < (X.tr j.1).length →
      ¬ WarpMatch L (X.appendLanes ds ev) (h, (X.tr h).length) j)
    (hnew : ∀ h ∈ ds, Ready L (X.appendLanes ds ev) (h, (X.tr h).length))
    (hshfl : ShflOk L (X.appendLanes ds ev)) (helect : ElectOk L (X.appendLanes ds ev))
    (hwarp : WarpBarOk L (X.appendLanes ds ev))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hlv : ∀ v pc k, (X.appendLanes ds ev).get v = some ⟨pc, k⟩ → k.laneValue = true →
      X.get v = some ⟨pc, k⟩ := fun v pc k h hk =>
    (appendLanes_get_kind (fun j hj => (hw j hj).ne (k' := k)
      (by cases k <;> simp_all [Kind.WarpColl, Kind.laneValue]))).mp h
  have hex : ∀ v pc, (X.appendLanes ds ev).get v = some ⟨pc, .exit⟩ → X.get v = some ⟨pc, .exit⟩ :=
    fun v pc h => (appendLanes_get_kind (fun j hj => (hw j hj).ne (k' := .exit) id)).mp h
  exact appendLanes_counted_extension_lane hX hd hds hlt (fun h hh => .of_warpColl (hw h hh)) hst
    hrel hrun hfresh hnew hshfl helect hwarp
    (Execution.voteOk_mono hX.vote le_appendLanes hlv hex)
    (Execution.warpValueOk_mono hX.warpValue le_appendLanes hlv hex) hasm

end
end PTX.Step
