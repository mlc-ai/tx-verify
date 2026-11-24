-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.Snoc
public import Core.Thread.SetMaxNReg
public import Lemmas.MBarrier.BarrierOrdinal
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Snoc.QuietReturnSink
public import Lemmas.Snoc.SnocResourceWaiting
public import Lemmas.Snoc.SnocSinkFrame
public import Lemmas.Snoc.SnocAsyncSilent
public import Lemmas.Snoc.SnocOrder
public import Lemmas.Snoc.Collectives
public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Snoc.SnocAfterCluster
public import Lemmas.Snoc.SnocResourceWaitEffects
public import Lemmas.Snoc.SnocConsistent
public import Lemmas.Snoc.ExtensionSnocFrame

@[expose] public section

/-! # Issuing a register request as a progress step

A proof tool. A thread that has made no register request and whose last event is a recorded
cluster barrier operation can issue one: the execution with the request appended is consistent and
strictly larger (`reg_issue_counted_extension`). The request stays the thread's last event; no
lane of its warp has returned from a matching request (DEP-SETMAXNREG-RENDEZVOUS needs the whole
warp), so the returns of the new request and of every request matching it are sinks of the waiting
graph. -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {g pc n inst : Nat} {inc : Bool} {r : Nat → Option Ref}

/-- A register request event. -/
abbrev regRequestEvent (pc : Nat) (inc : Bool) (n inst : Nat) : Event := ⟨pc, .setMaxReg inc n inst⟩

/-- Every request after the append is an unchanged old request or the new one. -/
theorem regIssue_request_cases {f : EvId} {pc' n' inst' : Nat} {inc' : Bool}
    (hf : SetMaxNReg.Request (X.snoc g (regRequestEvent pc inc n inst) r) f pc' inc' n' inst') :
    SetMaxNReg.Request X f pc' inc' n' inst' ∨
      (f = (g, (X.tr g).length) ∧ pc' = pc ∧ inc' = inc ∧ n' = n ∧ inst' = inst) := by
  change (X.snoc g (regRequestEvent pc inc n inst) r).get f = some ⟨pc', .setMaxReg inc' n' inst'⟩
    at hf
  rw [snoc_get] at hf
  split_ifs at hf with hnew
  · have heq := Option.some.inj hf
    cases heq
    exact .inr ⟨hnew, rfl, rfl, rfl, rfl⟩
  · exact .inl hf

/-- Every old request remains. -/
theorem regIssue_request_old {f : EvId} {pc' n' inst' : Nat} {inc' : Bool}
    (hf : SetMaxNReg.Request X f pc' inc' n' inst') :
    SetMaxNReg.Request (X.snoc g (regRequestEvent pc inc n inst) r) f pc' inc' n' inst' := by
  change (X.snoc g (regRequestEvent pc inc n inst) r).get f = _
  rw [snoc_get_old (len_of_get hf)]
  exact hf

theorem regIssue_ordinal_old {f : EvId} (hf : f.2 ≤ (X.tr f.1).length) :
    SetMaxNReg.ordinal (X.snoc g (regRequestEvent pc inc n inst) r) f = SetMaxNReg.ordinal X f := by
  unfold SetMaxNReg.ordinal
  rw [snoc_take hf]

theorem regIssue_sameRequest_old {e f : EvId} (h : SetMaxNReg.SameRequest L X e f) :
    SetMaxNReg.SameRequest L (X.snoc g (regRequestEvent pc inc n inst) r) e f := by
  obtain ⟨hw, ho, pc', inc', n', ei, fi, he, hf⟩ := h
  exact ⟨hw, by rw [regIssue_ordinal_old (len_of_get he).le,
    regIssue_ordinal_old (len_of_get hf).le]; exact ho,
    pc', inc', n', ei, fi, regIssue_request_old he, regIssue_request_old hf⟩

/-- Every old request matching the new one is its thread's last event: a return would need the
whole warp (DEP-SETMAXNREG-RENDEZVOUS, `DependencyOk.ready`), so the thread's lane would hold an
old request. -/
theorem regIssue_match_last (hX : Consistent L K A mem0 X)
    (hno : ∀ j pc' inc' n' inst', ¬ SetMaxNReg.Request X (g, j) pc' inc' n' inst')
    {f : EvId} (hf : SetMaxNReg.SameRequest L (X.snoc g (regRequestEvent pc inc n inst) r)
      (g, (X.tr g).length) f) :
    f.2 + 1 = ((X.snoc g (regRequestEvent pc inc n inst) r).tr f.1).length := by
  obtain ⟨hw, -, pc', inc', n', zi, fi, -, hfr⟩ := hf
  rcases regIssue_request_cases hfr with hold | ⟨rfl, -, -, -, -⟩
  · have hfg : f.1 ≠ g := by
      intro heq
      have hf : f = (g, f.2) := Prod.ext heq rfl
      exact hno f.2 pc' inc' n' fi (hf ▸ hold)
    rw [snoc_len, ite_eq_right hfg]
    have hlt := len_of_get hold
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
    obtain ⟨-, -, pc'', inc'', n'', ei, hi, -, hhr⟩ := hs
    exact hno j pc'' inc'' n'' hi hhr
  · simp [snoc_len]

/-! ## The waiting graph -/

local notation "Y" => Execution.snoc X g (regRequestEvent pc inc n inst) r
local notation "z" => (g, List.length (Execution.tr X g))

/-- The return of every request matching the new one is a sink: it is its thread's last
event. -/
theorem regIssue_return_sink (hvY : EffectValidity L Y) (hcY : ClusterHistoryOk L Y)
    (hlast : ∀ f, SetMaxNReg.SameRequest L Y z f → f.2 + 1 = ((Y).tr f.1).length) {f : EvId}
    (hf : SetMaxNReg.SameRequest L Y z f) : ∀ v, ¬ Waits L Y (.thread f, true) v := by
  have hfr := hf.2.2
  obtain ⟨pc', inc', n', zi, fi, -, hfr⟩ := hfr
  refine quiet_return_sink_of_effects hvY hcY hfr rfl (hlast f hf) fun cta j hc => ?_
  obtain ⟨pc'', group, dst, action, hres⟩ := hc.actual hvY.tmemPair
  rw [hfr] at hres
  cases hres

/-- The new request fills a need only of the requests matching it: every other node need is
filled by an event of the need's own kind, by an exit, by a recorded barrier, cluster or allocator
participant, by an object record or by an asynchronous stage, and no history of `X` names the new
request. -/
theorem regIssue_witness (hX : Consistent L K A mem0 X) {j : EvId}
    (h : Witness L Y (.thread z) j) : SetMaxNReg.SameRequest L Y z j := by
  obtain ⟨fills, hmem, -, hf⟩ := h
  have hnone : X.get z = none := List.getElem?_eq_none (le_refl _)
  have notX : ∀ {ev}, X.get z = some ev → False := fun h => by
    rw [hnone] at h; cases h
  have kindNew : ∀ {pc' k}, (Y).get z = some ⟨pc', k⟩ → Kind.setMaxReg inc n inst = k :=
    fun h => by rw [snoc_get_new] at h; cases h; rfl
  have mapped : ∀ {α : Type} (l : List α) (P : α → Ref → Prop),
      Need.node fills ∈ l.map (fun a => Need.node (P a)) → ∃ a ∈ l, fills = P a := by
    intro α l P hm
    obtain ⟨a, ha', he⟩ := List.mem_map.mp hm
    exact ⟨a, ha', (Need.node.inj he).symm⟩
  have exitCase : ∀ {u : EvId} {pc'}, Ref.thread z = .thread u →
      (Y).get u = some ⟨pc', .exit⟩ → False := by
    intro u pc' he hg
    cases he
    cases kindNew hg
  have maskCase : ∀ {Q V : Type} (c : Kind → Option (WarpPart Q V)),
      c (.setMaxReg inc n inst) = none → Need.node fills ∈ maskNeeds L c Y j → False := by
    intro Q V c hc hm
    unfold maskNeeds at hm
    generalize ((Y).get j).bind (fun ev => c ev.kind) = o at hm
    cases o with
    | none => simp at hm
    | some p =>
      obtain ⟨l, -, rfl⟩ := mapped _ _ hm
      obtain ⟨j', he, -, m, n, q, hat, ⟨⟨⟨ev, p', hg, hc', -⟩, -⟩, -⟩ | ⟨-, ⟨pc', hg⟩, -⟩⟩ := hf
      · cases he
        rw [snoc_get_new] at hg
        cases Option.some.inj hg
        rw [hc] at hc'
        cases hc'
      · exact exitCase he hg
  have tcCase : Need.node fills ∈ tcNeeds L Y j → False := by
    intro hm
    obtain ⟨l, -, rfl⟩ := mapped _ _ (by unfold tcNeeds at hm; exact hm)
    obtain ⟨j', he, ⟨ev, hg, hc⟩, -⟩ := hf
    cases he
    rw [snoc_get_new] at hg
    cases Option.some.inj hg
    simp [isTcColl] at hc
  unfold Needs at hmem
  cases hget : (Y).get j with
  | none => simp [hget] at hmem
  | some ev =>
  simp only [hget] at hmem
  obtain ⟨pc0, kd⟩ := ev
  cases kd
  case shfl => exact (maskCase shflClass rfl hmem).elim
  case vote => exact (maskCase voteClass rfl hmem).elim
  case voteMode => exact (maskCase voteClass rfl hmem).elim
  case redux => exact (maskCase reduxClass rfl hmem).elim
  case match_ => exact (maskCase matchClass rfl hmem).elim
  case elect mask inst' leader =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', pc', ld, he, hg⟩ := hf
    cases he
    cases kindNew hg
  case warpBar mask inst' =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, pc', hg⟩ := hf
    cases he
    cases kindNew hg
  case matrix op own recv =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, ⟨⟨ev, hg, hm⟩, -⟩ | ⟨⟨pc', hg⟩, -⟩⟩ := hf
    · cases he
      rw [snoc_get_new] at hg
      cases Option.some.inj hg
      cases hm
    · exact (exitCase he hg).elim
  case setMaxReg inc' n' inst' =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, hs⟩ := hf
    cases he
    exact SetMaxNReg.SameRequest.symm hs
  case bar id count mode =>
    simp only [KindNeeds, ctaBarNeeds] at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨l, -, rfl⟩ := mapped _ _ (by unfold ctaBarWarpNeeds at hm; exact hm)
      obtain ⟨i, rc, y, hi, -, he, -, hy | ⟨i', g', -, hi'⟩⟩ := hf
      · cases he
        exact (notX (hX.ctaBar.ref_present (List.mem_of_getElem? hi) hy).choose_spec).elim
      · cases he
        exact (notX (hX.ctaBar.ref_present (List.mem_of_getElem? hi')
          (by simp [CtaBarrier.Record.refs])).choose_spec).elim
    · cases mode with
      | arrive => simp at hm
      | sync =>
        rcases List.mem_cons.mp hm with h | hm
        · cases h
        obtain ⟨y, hy, hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨rc, hrc, hyr⟩ := List.mem_flatMap.mp hy
        unfold needsIf at hm
        split_ifs at hm
        · obtain rfl := Need.node.inj (List.mem_singleton.mp hm)
          cases hf
          exact (notX (hX.ctaBar.ref_present hrc hyr).choose_spec).elim
        · simp at hm
  case cluster op =>
    simp only [KindNeeds, clusterNeeds] at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨l, -, rfl⟩ := mapped _ _ (by unfold clusterWarpNeeds at hm; exact hm)
      obtain ⟨i, rc, y, hi, -, he, -, hy | ⟨i', g', -, hi'⟩⟩ := hf
      · cases he
        exact (notX (hX.cluster.ref_present (List.mem_of_getElem? hi) hy).choose_spec).elim
      · cases he
        exact (notX (hX.cluster.ref_present (List.mem_of_getElem? hi')
          (by simp [ClusterBarrier.Record.refs])).choose_spec).elim
    · cases op with
      | arrive => simp at hm
      | wait =>
        obtain ⟨y, hy, hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨rc, hrc, hyr⟩ := List.mem_flatMap.mp hy
        unfold needsIf at hm
        split_ifs at hm
        · obtain rfl := Need.node.inj (List.mem_singleton.mp hm)
          cases hf
          exact (notX (hX.cluster.ref_present hrc hyr).choose_spec).elim
        · simp at hm
  case bulkWait mode rem =>
    obtain ⟨i, -, hm⟩ := List.mem_flatMap.mp hmem
    unfold needsIf at hm
    split_ifs at hm
    · obtain ⟨p, -, rfl⟩ := mapped _ _ hm
      cases hf
    · simp at hm
  case asyncWait rem =>
    obtain ⟨i, -, hm⟩ := List.mem_flatMap.mp hmem
    unfold needsIf at hm
    split_ifs at hm
    · obtain ⟨p, -, rfl⟩ := mapped _ _ hm
      cases hf
    · simp at hm
  case wait m q ok acq sc =>
    cases ok
    · simp [KindNeeds] at hmem
    obtain ⟨rc, hrc, hm⟩ := List.mem_flatMap.mp hmem
    unfold needsIf at hm
    split_ifs at hm
    · obtain rfl := Need.node.inj (List.mem_singleton.mp hm)
      have hp : X.RefPresent rc.id := object_record_present hX.tma hrc
      rw [← hf] at hp
      obtain ⟨ev, hev⟩ := hp
      exact (notX hev).elim
    · simp at hm
  case tc t =>
    cases t
    case ld => exact (tcCase hmem).elim
    case st => exact (tcCase hmem).elim
    case waitLd => exact (tcCase hmem).elim
    case waitSt => exact (tcCase hmem).elim
    case resource group dst request =>
      simp only [KindNeeds, resourceNeeds] at hmem
      rcases List.mem_append.mp hmem with hcore | hresult
      · rcases List.mem_append.mp hcore with hm | hm
        · exact (tcCase hm).elim
        rcases List.mem_cons.mp hm with h | hm
        · cases h
        unfold needsIf at hm
        split_ifs at hm
        swap
        · simp at hm
        rcases List.mem_cons.mp hm with h | hm
        · cases h
        rcases List.mem_append.mp hm with hm | hm
        · cases group with
          | one => simp at hm
          | two =>
            obtain ⟨l, -, rfl⟩ := mapped _ _ hm
            obtain ⟨q, hq, ⟨-, he⟩ | ⟨-, he⟩⟩ := hf
            · obtain ⟨grp, hv⟩ := Tmem.Pair.Completed.valid hX.tmemPair (.inr ⟨q, hq, rfl⟩)
                (w := q.2) (by simp)
              rw [Ref.thread.inj he, hv.2.2.1 l] at hnone
              cases hnone
            · obtain ⟨grp, hv⟩ := Tmem.Pair.Completed.valid hX.tmemPair (.inr ⟨q, hq, rfl⟩)
                (w := q.1) (by simp)
              rw [Ref.thread.inj he, hv.2.2.1 l] at hnone
              cases hnone
        · cases request with
          | alloc cols =>
            obtain ⟨jj, -, hm⟩ := List.mem_flatMap.mp hm
            split_ifs at hm
            · obtain ⟨l, -, rfl⟩ := mapped _ _ hm
              obtain ⟨d, hd, he⟩ := hf
              have hv := ((hX.tmemPair.1 _).1 d (List.mem_of_getElem? hd)).2.2
              rw [Ref.thread.inj he, hv.2.2.1 l] at hnone
              cases hnone
            · simp at hm
          | _ => simp at hm
      · cases Tmem.Pair.allocResultNeeds_node L hresult
        obtain ⟨store, _, _, _, heq, hwrite⟩ := Tmem.Pair.AllocResultFill.written L hf
        cases heq
        cases kindNew hwrite
    all_goals simp [KindNeeds] at hmem
  all_goals simp [KindNeeds] at hmem

/-- The waiting successors of the new issue are its own return and the returns of the requests
matching it. -/
theorem regIssue_successors (hX : Consistent L K A mem0 X)
    (hrefl : SetMaxNReg.SameRequest L Y z z) {v : Ref × Bool}
    (h : Waits L Y (.thread z, false) v) :
    ∃ f, SetMaxNReg.SameRequest L Y z f ∧ v = (.thread f, true) := by
  rcases h with ⟨heq,hb,hb',_⟩ | ⟨_,_,i,j,hi,_,hij,hs,hl⟩ |
    ⟨i,j,hi,hj,hbar⟩ | ⟨_,_,i,j,hi,_,_,k,his,_⟩ |
    ⟨_,_,i,j,hi,_,_,k,hit,_⟩ | ⟨h1,h2,ha⟩ | ⟨h1,h2,m,ho⟩ |
    ⟨i,j,hi,hj,hcl⟩ | ⟨h1,h2,j,hj,hw⟩ | ⟨h1,h2,i,j,hi,hj,hw⟩ |
    ⟨h1,h2,i,j,hi,hj,hw⟩ | ⟨i,j,hi,hj,hw⟩ | ⟨h1,h2,i,j,hi,hj,cta,hp⟩ |
    ⟨h1,h2,i,j,hi,hj,hw⟩ | ⟨h1,h2,hi⟩
  · exact ⟨z, hrefl, Prod.ext heq.symm hb'⟩
  · contradiction
  · cases hi
    obtain ⟨ev, he⟩ := (ctaWaits_snoc_old hX.ctaBar hbar).1
    have hl := len_of_get he; simp at hl
  · cases hi
    have hl := ((snoc_shflK (g := g) (e := regRequestEvent pc inc n inst) (r := r)
      (by intros; intro h; cases h)).mp his).1
    simp at hl
  · cases hi
    have hl := ((snoc_tcK (g := g) (e := regRequestEvent pc inc n inst) (r := r)
      (by intro k h; cases h)).mp hit).lt
    simp at hl
  · cases h1
  · cases h1
  · cases hi
    obtain ⟨ev, he⟩ := (clusterWaits_snoc_old hX.cluster hcl).1
    have hl := len_of_get he; simp at hl
  · exact ⟨j, regIssue_witness hX hw, Prod.ext hj h2⟩
  · cases hi
    obtain ⟨-, mask, ii, ⟨p, he⟩, -⟩ := hw
    rw [snoc_get_new] at he
    cases he
  · cases h1
  · obtain ⟨hb, hb', hm⟩ := hw
    cases hi
    exact ⟨j, hm, Prod.ext hj hb'⟩
  · cases h1
  · cases h1
  · obtain ⟨-, -, i, p, he, -, -, hap, -⟩ := hi
    have hl := refPresent_issuer_lt hX.effectValidity (f := .async _ p)
      ((snoc_asyncPresent_of_not_tc (g := g) (e := regRequestEvent pc inc n inst) (r := r)
        (by intro k h; cases h)).mp hap)
    rw [← Ref.thread.inj he] at hl
    exact absurd hl (lt_irrefl _)

/-- The issue and the matching returns form a terminal suffix of the waiting graph. -/
def RegIssueTargets (L : Launch) (Q : Execution) (fresh : EvId) (u : Ref × Bool) : Prop :=
  u = (.thread fresh, false) ∨ ∃ f, SetMaxNReg.SameRequest L Q fresh f ∧ u = (.thread f, true)

/-- **Issuing a request is a sink frame** for its issue and the returns of the matching
requests. -/
theorem regIssue_sinkFrame (hX : Consistent L K A mem0 X) (hvY : EffectValidity L Y)
    (hcY : ClusterHistoryOk L Y)
    (hlast : ∀ f, SetMaxNReg.SameRequest L Y z f → f.2 + 1 = ((Y).tr f.1).length)
    (hrefl : SetMaxNReg.SameRequest L Y z z) : SinkFrame L K A X Y (RegIssueTargets L Y z) := by
  have hs : (Kind.setMaxReg inc n inst).AsyncSilent := trivial
  have hw : (regRequestEvent pc inc n inst).kind.ResourceWait := trivial
  refine snoc_sinkFrame (records := X.objects) hX ?_ ?_ SnocRecords.same
    (fun _ _ => (hs.snoc_asyncPresent (e := regRequestEvent pc inc n inst)).mp)
    (fun _ _ hj h => (hw.baseCausality_old hX.cluster hj).mp h)
    ⟨fun u => if u.2 then 1 else 0, ?_⟩
  · rintro ⟨x, (_ | _)⟩ (rfl : x = _)
    · exact .inl rfl
    · exact .inr ⟨z, hrefl, rfl⟩
  · rintro i (h | ⟨f, -, h⟩)
    · exact Ref.thread.inj (congrArg Prod.fst h)
    · cases congrArg Prod.snd h
  · intro u v hw hu
    rcases hu with rfl | ⟨f, hf, rfl⟩
    · obtain ⟨f, hf, rfl⟩ := regIssue_successors hX hrefl hw
      exact ⟨.inr ⟨f, hf, rfl⟩, by simp⟩
    · exact (regIssue_return_sink hvY hcY hlast hf v hw).elim

/-- A started, ready thread with no register request can issue its first request. -/
theorem reg_issue_counted_extension_of_started (hX : Consistent L K A mem0 X)
    (hg : g < L.threads) (hstarted : X.tr g ≠ [])
    (hready : LastReady L X g)
    (hno : ∀ j pc' inc' n' inst', ¬ SetMaxNReg.Request X (g, j) pc' inc' n' inst')
    {t t1 : TState} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 (regRequestEvent pc inc n inst) o)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g (regRequestEvent pc inc n inst) (fun _ => none))) :
    ∃ W, Consistent L K A mem0 W ∧ X.le W ∧ X.size L < W.size L := by
  have hw : (regRequestEvent pc inc n inst).kind.ResourceWait := trivial
  have hs : (Kind.setMaxReg inc n inst).AsyncSilent := trivial
  have heff := Kind.ResourceWait.preserved_of_started (e := regRequestEvent pc inc n inst)
    (r := fun _ => none) hw hX hstarted
  have hvY : EffectValidity L (X.snoc g (regRequestEvent pc inc n inst) (fun _ => none)) :=
    ⟨heff.tma, heff.tensor, heff.store, heff.clc, heff.tmemPair, heff.tcCommit⟩
  have hreq : SetMaxNReg.Request (X.snoc g (regRequestEvent pc inc n inst) (fun _ => none))
      (g, (X.tr g).length) pc inc n inst := by
    change (X.snoc g _ _).get _ = _
    rw [snoc_get_new]
  have hrefl := SetMaxNReg.SameRequest.refl (L := L) (by simpa using hg) hreq
  have hmatch := fun f => regIssue_match_last (L := L) (pc := pc) (inc := inc) (n := n)
    (inst := inst) (r := fun _ => none) (f := f) hX hno
  have horder := (regIssue_sinkFrame hX hvY heff.clusterHistory hmatch hrefl).orderOk hX.orderOk
  have hextra : ExtensionObligations L A (X.snoc g (regRequestEvent pc inc n inst) (fun _ =>
      none)) :=
    ExtensionObligations.snoc_frame hX (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun h => by cases h) heff.clc heff.tmemPairResult heff.tcRead heff.atomic heff.fenceSc
      heff.matrix (fun _ h => by cases h)
  have hnew : Returned (X.snoc g (regRequestEvent pc inc n inst) (fun _ => none)) (X.newId g) →
      Ready L (X.snoc g (regRequestEvent pc inc n inst) (fun _ => none)) (X.newId g) := by
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

/-- A ready thread with no register request can issue one after its cluster barrier. -/
theorem reg_issue_counted_extension (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    {source : Nat} {op : ClusterOp}
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨source, .cluster op⟩)
    (hready : LastReady L X g)
    (hno : ∀ j pc' inc' n' inst', ¬ SetMaxNReg.Request X (g, j) pc' inc' n' inst')
    {t t1 : TState} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 (regRequestEvent pc inc n inst) o)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g (regRequestEvent pc inc n inst) (fun _ => none))) :
    ∃ W, Consistent L K A mem0 W ∧ X.le W ∧ X.size L < W.size L := by
  apply reg_issue_counted_extension_of_started hX hg ?_ hready hno hrun hl he hasm
  intro he
  simp [Execution.get, he] at hlast

end
end PTX.Step
