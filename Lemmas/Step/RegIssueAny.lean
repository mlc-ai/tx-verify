-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.RegIssue

@[expose] public section

/-!
# A register request after any ready last event

`Step.reg_issue_counted_extension` issues a thread's first request after a recorded cluster
barrier operation. A kernel may issue several requests after other events (a named barrier, a
store, another request). The proof needs neither: the other effects of
appending a request are transported from the thread's having started, and the new request is the
last event of every request that matches it, because a matching request that is not last has
returned, so every lane of its warp, in particular the lane of the new request's thread, has a
request of the same ordinal before the new one, which is impossible.

* `Kind.ResourceWait.preserved_started`: `Kind.ResourceWait.preserved` with `X.tr g ≠ []` in place
  of the last event being a cluster barrier.
* `Step.regIssue_ordinal_lt`, `Step.regIssue_match_last_any`: `regIssue_match_last` without the
  hypothesis that the thread has no request.
* `Step.reg_issue_extension_any`: `reg_issue_counted_extension` for a thread that has started,
  whose last event is ready, with any number of earlier requests.
-/

namespace PTX
open AsyncCopy
noncomputable section

namespace Kind.ResourceWait
variable {L : Launch} {A : List Assumption} {K : Kernel} {mem0 : Mem0} {X : Execution}
  {g : Nat} {e : Event} {r : Nat → Option Ref}

private theorem clc (hw : e.kind.ResourceWait) (hX : Consistent L K A mem0 X)
    (hstarted : X.tr g ≠ []) : ClcOk L (X.snoc g e r) := by
  have hissue (i : EvId) (s : Clc.Spec) (ts : List Nat) :
      (X.snoc g e r).ClcIssue i s ts ↔ X.ClcIssue i s ts := hw.asyncSilent.snoc_clcIssue
  obtain ⟨ha, hr, he, hi, hl⟩ := hX.clc
  refine ⟨ha, ?_, ?_, ?_, ?_⟩
  · intro request answer hh
    obtain ⟨i, s, ts, hid, his⟩ := hr request answer hh
    exact ⟨i, s, ts, hid, (hissue ..).mpr his⟩
  · intro i hh
    obtain ⟨s, ts, his⟩ := he i hh
    exact ⟨s, ts, (hissue ..).mpr his⟩
  · intro i s ts hh
    exact hi i s ts ((hissue ..).mp hh)
  · rintro ⟨i, s, ts, his⟩ h hh hn
    apply hl ⟨i, s, ts, (hissue ..).mp his⟩ h hh
    by_cases hg : h = g
    · simpa only [hg] using hstarted
    · simpa only [snoc_tr, ite_eq_right hg] using hn

private theorem objectAction_eq (hw : e.kind.ResourceWait) (m : Loc) (id : Ref) :
    objectAction (X.snoc g e r) X.async m id = objectAction X X.async m id := by
  have hnew : X.get (g, (X.tr g).length) = none := List.getElem?_eq_none (le_refl _)
  cases id with
  | thread i =>
    simp only [objectAction]
    rw [snoc_get]
    split_ifs with hi
    · subst i; rw [hnew]
      obtain ⟨_, k⟩ := e
      cases k <;> first | rfl | exact (show False from hw).elim
    · rfl
  | async i p =>
    cases p <;> simp only [objectAction]
    all_goals first
      | rw [hw.asyncSilent.snoc_issuedBy]
      | (rw [snoc_get]
         split_ifs with hi
         · subst i; rw [hnew]
           obtain ⟨_, k⟩ := e
           cases k <;> first | rfl | exact (show False from hw).elim
         · rfl)

private theorem tma (hw : e.kind.ResourceWait) (hX : Consistent L K A mem0 X) :
    TmaOk (X.snoc g e r) := by
  refine ⟨?_, ?_, ?_, snoc_arriveOk hX.tma.2.2.2⟩
  · simpa only [hw.asyncSilent.snoc_issuedBy, snoc_async] using hX.tma.1
  · simpa only [TcEffectsOk, snoc_async, snoc_mmaIssue hw.noTc, snoc_cpIssue hw.noTc,
      snoc_shiftIssue hw.noTc] using hX.tma.2.1
  · intro m
    obtain ⟨hv, hm, hc⟩ := hX.tma.2.2.1 m
    refine ⟨hv, ?_, ?_⟩
    · intro rec hr
      simpa only [snoc_async, objectAction_eq hw] using hm rec hr
    · intro id action hi
      apply hc id action
      simpa only [snoc_async, objectAction_eq hw] using hi

/-- Complete non-resource effect transport for a thread that has started
(`Kind.ResourceWait.preserved` without the cluster barrier as the last event). -/
theorem preserved_started (hw : e.kind.ResourceWait) (hX : Consistent L K A mem0 X)
    (hstarted : X.tr g ≠ []) : NonResourceEffects L A X (X.snoc g e r) := by
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x
          f) := fun hf => hw.baseCausality_old hX.cluster hf
  have helect {i : EvId} {pc mask label leader : Nat} :
      (X.snoc g e r).Elect i pc mask label leader ↔ X.Elect i pc mask label leader :=
    ⟨fun h => snoc_get_not_kind h (hw.ne id), Execution.le_get le_snoc⟩
  have hwarp {i : EvId} {mask label : Nat} :
      (X.snoc g e r).WarpBar i mask label ↔ X.WarpBar i mask label := snoc_kind_iff (hw.ne id)
  have hmat : isMatrix e = false := by
    obtain ⟨pc, k⟩ := e
    cases k <;> simp_all [Kind.ResourceWait, isMatrix]
  refine ⟨hX.cluster.preserving le_snoc rfl, by simpa only [ElectOk, helect] using hX.elect,
    by simpa only [WarpBarOk, hwarp] using hX.warpBar, clc hw hX hstarted, ?_, ?_,
    hX.atomic.snoc hX.store hX.tma.1 (fun _ _ _ => hw.ne id),
    hX.fenceSc.snoc (fun _ => hw.ne id) fun _ _ hb h => (hbo hb).mp h,
    hX.matrix.snoc hmat, hX.reduce.snoc (fun _ => hw.ne id),
    hX.tmemPair.mono le_snoc (fun _ => rfl) rfl,
    hX.tmemPairResult.snoc_not_wr (fun _ _ _ h => hw.ne id (congrArg Event.kind h)),
    ?_, readOk_snoc hX.tcRead hX.tcCommit hX.tma.2.2.1 hX.tma.2.1 hbo
      (fun _ _ _ _ h => (hw.ne id (congrArg Event.kind h)).elim),
    tma hw hX, readPreserved_snoc hX.tcCommit hX.tma.2.2.1 hbo⟩
  · intro i observation hi
    obtain ⟨⟨addr, hissue⟩, rest⟩ := hX.tensor i observation hi
    exact ⟨⟨addr, hw.asyncSilent.snoc_tensorIssue.mpr hissue⟩, rest⟩
  · intro i observation hi
    obtain ⟨⟨addr, hissue⟩, rest⟩ := hX.store i observation hi
    exact ⟨⟨addr, hw.asyncSilent.snoc_storeIssue.mpr hissue⟩, rest⟩
  · simp only [CommitOk, snoc_tracksMma_of_not_tc hw.noTc, snoc_commit hw.noTc, snoc_async]
    exact hX.tcCommit

end Kind.ResourceWait

namespace Step
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {g pc n inst : Nat} {inc : Bool} {r : Nat → Option Ref}

/-- A request of a thread has a smaller ordinal than the position after the thread's last event. -/
theorem regIssue_ordinal_lt {j pc' inst' n' : Nat} {inc' : Bool}
    (h : SetMaxNReg.Request X (g, j) pc' inc' n' inst') :
    SetMaxNReg.ordinal X (g, j) < SetMaxNReg.ordinal X (g, (X.tr g).length) := by
  have hget : (X.tr g)[j]? = some ⟨pc', .setMaxReg inc' n' inst'⟩ := h
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  unfold SetMaxNReg.ordinal
  have h1 : (X.tr g).take (j + 1) =
      (X.tr g).take j ++ [(⟨pc', .setMaxReg inc' n' inst'⟩ : Event)] := by
    rw [List.take_add_one, hget]
    rfl
  have h2 : ((X.tr g).take (j + 1)).countP SetMaxNReg.isRequest =
      ((X.tr g).take j).countP SetMaxNReg.isRequest + 1 := by
    rw [h1, List.countP_append]
    simp [SetMaxNReg.isRequest]
  have h3 : ((X.tr g).take (j + 1)).countP SetMaxNReg.isRequest ≤
      ((X.tr g).take (X.tr g).length).countP SetMaxNReg.isRequest :=
    (List.take_sublist_take_left (by omega)).countP_le
  simp only at h2 h3 ⊢
  omega

/-- **Every request matching a new request is its thread's last event**, whatever requests the
thread made before: a matching request that is not last has returned, so the lane of the new
request's thread has a request of the same ordinal before it, but its ordinal is larger
(`regIssue_ordinal_lt`). `regIssue_match_last` without the hypothesis that the thread made none. -/
theorem regIssue_match_last_any (hX : Consistent L K A mem0 X) {f : EvId}
    (hf : SetMaxNReg.SameRequest L (X.snoc g (regRequestEvent pc inc n inst) r)
      (g, (X.tr g).length) f) :
    f.2 + 1 = ((X.snoc g (regRequestEvent pc inc n inst) r).tr f.1).length := by
  obtain ⟨hw, ho, pc', inc', n', zi, fi, -, hfr⟩ := hf
  rcases regIssue_request_cases hfr with hold | ⟨rfl, -, -, -, -⟩
  · have hlt := len_of_get hold
    have h1 := regIssue_ordinal_old (X := X) (g := g) (pc := pc) (inc := inc) (n := n)
      (inst := inst) (r := r) (f := (g, (X.tr g).length)) le_rfl
    have h2 := regIssue_ordinal_old (X := X) (g := g) (pc := pc) (inc := inc) (n := n)
      (inst := inst) (r := r) (f := f) hlt.le
    have hord : SetMaxNReg.ordinal X f = SetMaxNReg.ordinal X (g, (X.tr g).length) := by
      rw [← h1, ← h2]
      exact ho.symm
    by_cases hfg : f.1 = g
    · exfalso
      have hf' : f = (g, f.2) := Prod.ext hfg rfl
      have hold' : SetMaxNReg.Request X (g, f.2) pc' inc' n' fi := by
        rw [← hf']
        exact hold
      have := regIssue_ordinal_lt hold'
      rw [← hf'] at this
      omega
    · rw [snoc_len, ite_eq_right hfg]
      by_contra hne
      have hret : Returned X f := by
        unfold Returned
        rw [hold]
        exact (by omega : f.2 + 1 < (X.tr f.1).length)
      obtain ⟨j, -, hs⟩ := (SetMaxNReg.ready_iff hold).1 (hX.dependency.ready f hret)
        (laneOf L g) (Nat.mod_lt _ (by decide))
      have hgw : g = warpLane L f.1 (laneOf L g) :=
        eq_warpLane_of_sameWarp ⟨⟨hw.1.2.1, hw.1.1, hw.1.2.2.symm⟩, hw.2.symm⟩ rfl
      rw [← hgw] at hs
      obtain ⟨-, ho2, pc'', inc'', n'', ei, hi, -, hhr⟩ := hs
      have := regIssue_ordinal_lt hhr
      omega
  · simp [snoc_len]

local notation "Y" => Execution.snoc X g (regRequestEvent pc inc n inst) (fun _ => none)

/-- **A thread that has started, whose last event is ready, issues a register request**: a counted
extension, whatever its last event is and however many requests it made before.
`reg_issue_counted_extension` for a thread whose last event is not a cluster barrier operation
and that may have made requests before. -/
theorem reg_issue_extension_any (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hstarted : X.tr g ≠ []) (hready : LastReady L X g)
    {t t1 : TState} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 (regRequestEvent pc inc n inst) o)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g (regRequestEvent pc inc n inst) (fun _ => none))) :
    ∃ W, Consistent L K A mem0 W ∧ X.le W ∧ X.size L < W.size L := by
  have hw : (regRequestEvent pc inc n inst).kind.ResourceWait := trivial
  have hs : (Kind.setMaxReg inc n inst).AsyncSilent := trivial
  have heff := Kind.ResourceWait.preserved_started (e := regRequestEvent pc inc n inst)
    (r := fun _ => none) hw hX hstarted
  have hvY : EffectValidity L Y :=
    ⟨heff.tma, heff.tensor, heff.store, heff.clc, heff.tmemPair, heff.tcCommit⟩
  have hreq : SetMaxNReg.Request Y (g, (X.tr g).length) pc inc n inst := by
    change (X.snoc g _ _).get _ = _
    rw [snoc_get_new]
  have hrefl := SetMaxNReg.SameRequest.refl (L := L) (by simpa using hg) hreq
  have hmatch := fun f => regIssue_match_last_any (L := L) (g := g) (pc := pc) (inc := inc)
    (n := n) (inst := inst) (r := fun _ => none) (f := f) hX
  have horder := (regIssue_sinkFrame hX hvY heff.clusterHistory hmatch hrefl).orderOk hX.orderOk
  have hextra : ExtensionObligations L A Y :=
    ExtensionObligations.snoc_frame hX (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun h => by cases h) heff.clc heff.tmemPairResult heff.tcRead heff.atomic heff.fenceSc
      heff.matrix (fun _ h => by cases h)
  have hnew : Returned Y (X.newId g) → Ready L Y (X.newId g) := by
    intro hr
    unfold Returned at hr
    rw [snoc_get_new] at hr
    change (X.tr g).length + 1 < _ at hr
    simp [snoc_len] at hr
  have hY := consistent_snoc_preserving hX hg hrun hl he (by intros; intro h; cases h)
    (fun h => by cases h) hready hnew
    (fun v a bs h => (hs.snoc_memReads (X := X) (g := g) (e := ⟨pc, _⟩) (r := fun _ => none)
      (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)).mp h)
    (fun v a bs => hs.snoc_memWrites (X := X) (g := g) (e := ⟨pc, _⟩) (r := fun _ => none)
      (fun _ _ h => by cases h) (fun _ _ _ h => by cases h))
    (fun l v w hw' => hs.modelCausality_snoc_old (fun hf => hw.baseCausality_old hX.cluster hf)
      (snoc_allocResultBefore_old hX.dependency.ready)
      (refPresent_issuer_lt hX.effectValidity hw'))
    horder hasm heff.tma hextra
  refine ⟨_, hY, le_snoc, ?_⟩
  rw [size_snoc hX hg rfl]
  omega

end Step

end
end PTX
