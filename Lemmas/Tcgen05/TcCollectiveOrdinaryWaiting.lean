-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcExtend
public import Lemmas.MBarrier.BarWaiting
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Snoc.SnocBlockingConsistent
public import Lemmas.Snoc.SnocObjectWaiting

@[expose] public section

section
/-! The lanes of a warp: a thread of the warp of `h` is one of `warpLanes L h`, and conversely. -/
namespace PTX
variable {L : Launch}

private theorem block_pos {g : Nat} (hg : g < L.threads) : 0 < L.block := by
  rcases Nat.eq_zero_or_pos L.block with h | h
  · unfold Launch.threads at hg; rw [h, Nat.mul_zero] at hg; omega
  · exact h

/-- A thread of the warp of `h` is a lane of `warpLanes L h`. -/
theorem mem_warpLanes_of_sameWarp {g h : Nat} (hw : SameWarp L g h) : g ∈ warpLanes L h := by
  have hb := block_pos hw.1.1
  refine List.mem_map.mpr ⟨laneOf L g, List.mem_range.mpr ?_, ?_⟩
  · have hm := Nat.mod_lt g hb
    have hd := Nat.div_add_mod (g % L.block) 32
    have hs := hw.2
    unfold warpSize laneOf
    rw [lt_min_iff]
    omega
  · exact (sameWarp_lane L (sameWarp_symm hw)).symm

/-- A lane of `warpLanes L h` is a thread of the warp of `h`. -/
theorem sameWarp_of_mem_warpLanes {g h : Nat} (hm : g ∈ warpLanes L h) (hg : g < L.threads)
    (hh : h < L.threads) : SameWarp L g h := by
  have hb := block_pos hh
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
  rw [List.mem_range] at hl
  unfold warpSize at hl
  rw [lt_min_iff] at hl
  have e1 := Nat.div_add_mod h L.block
  have e2 := Nat.div_add_mod (h % L.block) 32
  have hr := Nat.mod_lt h hb
  have hdm : warpLane L h l / L.block = h / L.block ∧
      warpLane L h l % L.block = h % L.block / 32 * 32 + l := by
    rw [Nat.div_mod_unique hb]
    unfold warpLane laneOf
    constructor <;> omega
  refine ⟨⟨hg, hh, hdm.1⟩, ?_⟩
  rw [hdm.2]
  omega

end PTX
end

section
/-! The return of a warp-collective `tcgen05` event (`isTcColl`) starts no waiting edge once its
thread has no later event and no allocator order edge leaves it: such an event has no mbarrier
action, cluster-barrier record, memory write or fence. -/
namespace PTX.TcCollective
noncomputable section
open AsyncCopy
variable {L : Launch} {X : Execution} {f : EvId} {ev : Event}

theorem kind_of_coll {e : Event} (h : isTcColl e = true) : ∃ k, e.kind = .tc k := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> first | exact ⟨_, rfl⟩ | cases h

private theorem other (hf : X.get f = some ev) (hc : isTcColl ev = true) {pc : Nat} {k : Kind}
    (h : X.get f = some ⟨pc, k⟩) (hk : isTcColl ⟨pc, k⟩ = false) : False := by
  rw [hf] at h
  cases h
  rw [hc] at hk
  cases hk

theorem no_objectAction (hf : X.get f = some ev) (hc : isTcColl ev = true) (m : Loc) :
    objectAction X X.async m (.thread f) = none := by
  obtain ⟨k, hk⟩ := kind_of_coll hc
  obtain ⟨pc, kd⟩ := ev
  simp only at hk
  subst hk
  simp only [objectAction, hf]

theorem no_object_before (ht : TmaOk X) (hf : X.get f = some ev) (hc : isTcColl ev = true)
    (m : Loc) (w : Ref) : ¬ MBarrier.Before (X.objects m) (.thread f) w := by
  rintro ⟨a, b, ra, rb, ha, hid, _⟩
  obtain ⟨ho, -⟩ := (ht.2.2.1 m).2.1 ra (List.mem_of_getElem? ha)
  rw [hid, no_objectAction hf hc] at ho
  cases ho

private theorem no_cluster (hcl : ClusterHistoryOk L X) (hf : X.get f = some ev)
    (hc : isTcColl ev = true) {j : EvId} {b : Bool} : ¬ ClusterWaits L X f j true b := by
  have noRecord {c : Nat} {record : ClusterBarrier.Record EvId}
      (hr : record ∈ X.clusters c) (he : f ∈ record.refs) : False := by
    rcases hcl.ref_operation hr he with ⟨pc, op, hp⟩ | ⟨pc, hp⟩
    all_goals exact other hf hc hp rfl
  rintro ⟨_, _, hh⟩
  rcases hh with ⟨c, i, j, record, q, hr, hq, hij, he, hf, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩
  · exact noRecord (List.mem_of_getElem? hr) he
  all_goals cases hb

private theorem no_memWrites (hf : X.get f = some ev) (hc : isTcColl ev = true) (a : Acc)
    (bs : List Byte) : ¬ X.MemWrites (.thread f) a bs := by
  rintro (⟨pc, hp⟩ | ⟨old, pc, hp⟩)
  all_goals exact other hf hc hp rfl

private theorem no_threadFence (hf : X.get f = some ev) (hc : isTcColl ev = true)
    (sem : FenceSem) (s : MbarScope) : ¬ X.ThreadFence f sem s := by
  rintro ⟨pc, hp⟩
  exact other hf hc hp rfl

private theorem no_sync (hf : X.get f = some ev) (hc : isTcColl ev = true) (j : EvId) :
    ¬ synchronizesWith L X f j := by
  rintro ⟨a, b, bs, cs, hw, -, -, -, -, -, -, -, -, -⟩
  exact no_memWrites hf hc a bs hw

private theorem no_fenceSync (hf : X.get f = some ev) (hc : isTcColl ev = true) (j : EvId) :
    ¬ FenceSync L X f j := by
  rintro (⟨w, r, a, b, bs, cs, se, sf, hw, -, -, hhead, -⟩ | ⟨⟨s, s', hsc, -, -⟩, -⟩)
  · rcases hhead with ⟨rfl, -, -⟩ | ⟨sem, hfe, -, -, -⟩
    · exact no_memWrites hf hc a bs hw
    · exact no_threadFence hf hc sem se hfe
  · exact no_threadFence hf hc .sc s hsc

/-- The return of a warp-collective `tcgen05` event with no later event of its thread, no
mbarrier order edge and no allocator order edge out of it is a sink. -/
theorem return_sink (hcl : ClusterHistoryOk L X) (hf : X.get f = some ev)
    (hc : isTcColl ev = true) (hlast : (X.tr f.1).length ≤ f.2 + 1)
    (hobj : ∀ m w, ¬ MBarrier.Before (X.objects m) (.thread f) w)
    (hord : ∀ cta j, ¬ Tmem.Pair.Precedes L X cta f j) (v : Ref × Bool) :
    ¬ Waits L X (.thread f, true) v := by
  rintro (⟨_, hb, _, _⟩ | ⟨_, _, i, j, hi, _, hij, hs, hl⟩ | ⟨i, j, hi, _, hb⟩ |
    ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨_, _, hso⟩ | ⟨_, _, m, hb⟩ | ⟨i, j, hi, _, hw⟩ |
    ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨_, _, i, j, hi, _, hsc⟩ | ⟨i, j, hi, _, hr⟩ |
    ⟨_, _, i, j, hi, _, cta, hp⟩ | ⟨_, _, i, j, hi, _, hfs⟩ | ⟨hb, _⟩)
  · cases hb
  · cases hi
    rw [← hij] at hl
    omega
  · rcases hb.2.2 with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩ <;> cases hb
  · cases hb
  · cases hb
  · rcases hso with ⟨_, hb, _, _⟩ | ⟨_, _, hedge⟩
    · cases hb
    · exact hedge
  · exact hobj m _ hb
  · cases hi
    exact no_cluster hcl hf hc hw
  · cases hb
  · cases hb
  · cases hi
    exact no_sync hf hc j hsc
  · cases hr.1
  · cases hi
    exact hord cta j hp
  · cases hi
    exact no_fenceSync hf hc j hfs
  · cases hb

end
end PTX.TcCollective
end

section
/-! Appending a warp-collective `tcgen05` event of thread `g`: its new return and the returns of
the lanes of its warp that wait at the same instance are sinks (`tcSink_sink`), and its issue only
reaches them (`snoc_tccoll_from_issue`). -/
namespace PTX
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}
open AsyncCopy
variable {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- The new event, if a collective, is instance `countP isTcColl` of its thread. -/
theorem snoc_tcK_new {k : Nat} (h : (X.snoc g e r).TcK (g, (X.tr g).length) k) :
    k = (X.tr g).countP isTcColl := by
  obtain ⟨-, hcnt⟩ := h
  rw [snoc_take (v := (g, (X.tr g).length)) (le_refl _)] at hcnt
  simpa using hcnt.symm

/-- Thread `g` has not executed the collective instance its next collective belongs to. -/
theorem not_tcK_last {i : Nat} (h : X.TcK (g, i) ((X.tr g).countP isTcColl)) : False := by
  obtain ⟨⟨ev, hget, hc⟩, hcnt⟩ := h
  unfold Execution.get at hget
  simp only at hget hcnt
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hget
  have := countP_take_lt (p := isTcColl) hi (by rw [hget]; exact hc)
  omega

/-- A warp-collective `tcgen05` event followed by another event of its thread has returned. -/
theorem returned_of_tcColl {j : EvId} {ev : Event} (hj : X.get j = some ev)
    (hc : isTcColl ev = true) (hl : j.2 + 1 < (X.tr j.1).length) : Returned X j := by
  obtain ⟨k, hk⟩ := TcCollective.kind_of_coll hc
  obtain ⟨pc, kd⟩ := ev
  simp only at hk
  subst hk
  unfold Returned
  rw [hj]
  cases k <;> simp_all [isTcColl, Kind.resume, TcKind.resume]

/-- A warp-collective `tcgen05` event needs the event of each lane of its warp of the same
instance (`tcNeeds`). -/
theorem tcNeed_mem {j : EvId} {ev : Event} (hj : X.get j = some ev) (hc : isTcColl ev = true)
    {h : Nat} (hh : h ∈ warpLanes L j.1) :
    Need.node (fun x => ∃ i, x = .thread (h, i) ∧
      X.TcK (h, i) (((X.tr j.1).take j.2).countP isTcColl)) ∈ Needs L X j := by
  have hm : Need.node (fun x => ∃ i, x = .thread (h, i) ∧
      X.TcK (h, i) (((X.tr j.1).take j.2).countP isTcColl)) ∈ tcNeeds L X j :=
    List.mem_map.mpr ⟨h, hh, rfl⟩
  simp only [Needs, hj]
  obtain ⟨k, hk⟩ := TcCollective.kind_of_coll hc
  obtain ⟨pc, kd⟩ := ev
  simp only at hk
  subst hk
  cases k <;> first
    | exact hm
    | exact List.mem_append_left _ (List.mem_append_left _ hm)
    | simp [isTcColl] at hc

/-- No lane of `g`'s warp has an event after its own instance of `g`'s next collective: that
instance would have returned and so be ready, while its need for `g`'s event of the instance is
unfilled. -/
theorem tc_blocked (hX : Consistent L K A mem0 X) {h j : Nat} (hw : SameWarp L g h)
    (hk : X.TcK (h, j) ((X.tr g).countP isTcColl)) (hj : j + 1 < (X.tr h).length) : False := by
  obtain ⟨⟨ev, hget, hc⟩, hcnt⟩ := hk
  have hready := hX.dependency.ready _ (returned_of_tcColl hget hc hj)
  obtain ⟨x, -, i, rfl, hi⟩ := hready _ (tcNeed_mem hget hc (mem_warpLanes_of_sameWarp hw))
  simp only at hcnt
  rw [hcnt] at hi
  exact not_tcK_last hi

/-- A new collective return and peer returns blocked at this instance are sinks. -/
def TcSink (L : Launch) (X : Execution) (g : Nat) (v : Ref × Bool) : Prop :=
  v = (.thread (g, (X.tr g).length), true) ∨
    ∃ f, v = (.thread f, true) ∧ f.2 < (X.tr f.1).length ∧ SameWarp L g f.1 ∧
      X.TcK f ((X.tr g).countP isTcColl)

theorem tcSink_sink (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hc : isTcColl e = true) {v w : Ref × Bool} (hv : TcSink L X g v) :
    ¬ Waits L (X.snoc g e r) v w := by
  have hcl : ClusterHistoryOk L (X.snoc g e r) := hX.cluster.preserving le_snoc rfl
  rcases hv with rfl | ⟨f, rfl, hfo, hw, hk⟩
  · refine TcCollective.return_sink hcl snoc_get_new hc ?_ ?_ ?_ w
    · simp [snoc_len]
    · rintro m f ⟨a, b, ra, rb, ha, hid, _⟩
      exact snoc_fresh_object_id hX.tma (List.mem_of_getElem? ha) hid
    · intro cta j hp
      obtain ⟨x, hx, lane, hl⟩ := hp.recorded.1
      have hget := ((hX.tmemPair.1 cta).1 x hx).2.2.2.2.1 lane
      rw [hl] at hget
      exact absurd (len_of_get hget) (by simp)
  · have hfg : f.1 ≠ g := by
      intro hfg
      have hf : f = (g, f.2) := Prod.ext hfg rfl
      rw [hf] at hk
      exact not_tcK_last hk
    obtain ⟨⟨ev, hp, hcoll⟩, _⟩ := id hk
    refine TcCollective.return_sink hcl (by rw [snoc_get_old hfo]; exact hp) hcoll ?_ ?_ ?_ w
    · rw [snoc_len, ite_eq_right hfg]
      by_contra hlt
      exact tc_blocked hX hw hk (by omega)
    · exact fun m w hb => TcCollective.no_object_before hX.tma hp hcoll m w hb
    · intro cta j hpre
      obtain ⟨x, hx, hpx⟩ := (Tmem.Pair.Precedes.recorded hpre).1
      obtain ⟨i, hi⟩ :=
        (((hX.tmemPair.1 cta).1 x hx).2.2).tcDone hpx hk g hg (sameWarp_symm hw)
      exact not_tcK_last hi

/-- The appended `tcgen05` event fills a need of another event only when it is a collective and
that event is a lane of its warp blocked at the same instance: every other node need is filled by
an event of the need's own kind, by an exit, by a recorded barrier, cluster or allocator
participant, by an object record or by an asynchronous stage. -/
theorem snoc_tc_witness (hX : Consistent L K A mem0 X) (hg : g < L.threads) {t : TcKind}
    (ht : e.kind = .tc t) {j : EvId} (h : Witness L (X.snoc g e r) (.thread (X.newId g)) j) :
    j = X.newId g ∨ (isTcColl e = true ∧ TcSink L X g (.thread j, true)) := by
  obtain ⟨fills, hmem, -, hf⟩ := h
  have hnone : X.get (X.newId g) = none := List.getElem?_eq_none (le_refl _)
  have notX : ∀ {ev}, X.get (X.newId g) = some ev → False := fun h => by
    rw [hnone] at h; cases h
  have notKind : ∀ {pc k}, (X.snoc g e r).get (X.newId g) = some ⟨pc, k⟩ →
      (∀ t, k ≠ .tc t) → False := by
    intro pc k h hk
    rw [snoc_get_new] at h
    cases Option.some.inj h
    exact hk t ht
  have mapped : ∀ {α : Type} (l : List α) (P : α → Ref → Prop),
      Need.node fills ∈ l.map (fun a => Need.node (P a)) → ∃ a ∈ l, fills = P a := by
    intro α l P hm
    obtain ⟨a, ha', he⟩ := List.mem_map.mp hm
    exact ⟨a, ha', (Need.node.inj he).symm⟩
  have maskCase : ∀ {Q V : Type} (c : Kind → Option (WarpPart Q V)), (∀ t, c (.tc t) = none) →
      Need.node fills ∈ maskNeeds L c (X.snoc g e r) j → False := by
    intro Q V c hct hm
    unfold maskNeeds at hm
    generalize ((X.snoc g e r).get j).bind (fun ev => c ev.kind) = o at hm
    cases o with
    | none => simp at hm
    | some p =>
      obtain ⟨l, -, rfl⟩ := mapped _ _ hm
      obtain ⟨j', he, -, m, n, q, hat, ⟨⟨⟨ev, p', hge, hc', -⟩, -⟩, -⟩ | ⟨-, ⟨pc, hge⟩, -⟩⟩ := hf
      · rw [← Ref.thread.inj he, snoc_get_new] at hge
        cases Option.some.inj hge
        rw [ht, hct] at hc'
        cases hc'
      · rw [← Ref.thread.inj he] at hge
        exact notKind hge (fun _ h => Kind.noConfusion h)
  have tcCase : ∀ {pc0 : Nat} {k0 : Kind}, (X.snoc g e r).get j = some ⟨pc0, k0⟩ →
      isTcColl ⟨pc0, k0⟩ = true → Need.node fills ∈ tcNeeds L (X.snoc g e r) j →
      j = X.newId g ∨ (isTcColl e = true ∧ TcSink L X g (.thread j, true)) := by
    intro pc0 k0 hgj hcj hm
    obtain ⟨l, hl, rfl⟩ := mapped _ _ (by unfold tcNeeds at hm; exact hm)
    obtain ⟨j', he, hk⟩ := hf
    have hid := Ref.thread.inj he
    rw [← hid] at hk
    have hce : isTcColl e = true := by
      obtain ⟨⟨ev, hge, hc⟩, -⟩ := hk
      rw [snoc_get_new] at hge
      cases Option.some.inj hge
      exact hc
    have hcount := snoc_tcK_new hk
    rcases snoc_index_cases (len_of_get hgj) with hold | hnew
    · right
      refine ⟨hce, .inr ⟨j, rfl, hold, ?_, ?_⟩⟩
      · have hlg : l = g := (congrArg Prod.fst hid).symm
        subst hlg
        have hj1 : j.1 < L.threads := by
          by_contra hn
          have ht0 := hX.outside j.1 (Nat.le_of_not_gt hn)
          rw [ht0] at hold
          simp at hold
        exact sameWarp_of_mem_warpLanes hl hg hj1
      · refine ⟨⟨_, by rw [← snoc_get_old hold]; exact hgj, hcj⟩, ?_⟩
        rw [← snoc_take hold.le]
        exact hcount
    · exact .inl hnew
  unfold Needs at hmem
  cases hget : (X.snoc g e r).get j with
  | none => simp [hget] at hmem
  | some ev =>
  simp only [hget] at hmem
  obtain ⟨pc, kd⟩ := ev
  cases kd
  case tc t' =>
    cases t'
    case ld => exact tcCase hget rfl hmem
    case st => exact tcCase hget rfl hmem
    case waitLd => exact tcCase hget rfl hmem
    case waitSt => exact tcCase hget rfl hmem
    case resource group dst request =>
      simp only [KindNeeds, resourceNeeds] at hmem
      rcases List.mem_append.mp hmem with hc | hr
      · rcases List.mem_append.mp hc with hm | hm
        · exact tcCase hget rfl hm
        exfalso
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
      · cases Tmem.Pair.allocResultNeeds_node L hr
        obtain ⟨store, site, dst, bytes, heq, hwrite⟩ := Tmem.Pair.AllocResultFill.written L hf
        cases heq
        exact (notKind hwrite (fun _ h => Kind.noConfusion h)).elim
    all_goals simp [KindNeeds] at hmem
  all_goals exfalso
  case shfl => exact maskCase shflClass (fun _ => rfl) hmem
  case vote => exact maskCase voteClass (fun _ => rfl) hmem
  case voteMode => exact maskCase voteClass (fun _ => rfl) hmem
  case redux => exact maskCase reduxClass (fun _ => rfl) hmem
  case match_ => exact maskCase matchClass (fun _ => rfl) hmem
  case elect mask inst leader =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', pc', ld, he, hge⟩ := hf
    rw [← Ref.thread.inj he] at hge
    exact notKind hge (fun _ h => Kind.noConfusion h)
  case warpBar mask inst =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, pc', hge⟩ := hf
    rw [← Ref.thread.inj he] at hge
    exact notKind hge (fun _ h => Kind.noConfusion h)
  case matrix op own recv =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, ⟨⟨ev, hge, hm⟩, -⟩ | ⟨⟨pc', hge⟩, -⟩⟩ := hf
    · rw [← Ref.thread.inj he, snoc_get_new] at hge
      cases Option.some.inj hge
      obtain ⟨pce, kde⟩ := e
      simp only at ht
      subst ht
      cases hm
    · rw [← Ref.thread.inj he] at hge
      exact notKind hge (fun _ h => Kind.noConfusion h)
  case setMaxReg inc n inst =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, -, -, pc', inc', n', ei, fi, -, hge⟩ := hf
    rw [← Ref.thread.inj he] at hge
    exact notKind hge (fun _ h => Kind.noConfusion h)
  case bar id count mode =>
    simp only [KindNeeds, ctaBarNeeds] at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨l, -, rfl⟩ := mapped _ _ (by unfold ctaBarWarpNeeds at hm; exact hm)
      obtain ⟨i, rc, y, hi, -, he, -, hy | ⟨i', g', -, hi'⟩⟩ := hf
      · cases he
        exact notX (hX.ctaBar.ref_present (List.mem_of_getElem? hi) hy).choose_spec
      · cases he
        exact notX (hX.ctaBar.ref_present (List.mem_of_getElem? hi')
          (by simp [CtaBarrier.Record.refs])).choose_spec
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
          exact notX (hX.ctaBar.ref_present hrc hyr).choose_spec
        · simp at hm
  case cluster op =>
    simp only [KindNeeds, clusterNeeds] at hmem
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨l, -, rfl⟩ := mapped _ _ (by unfold clusterWarpNeeds at hm; exact hm)
      obtain ⟨i, rc, y, hi, -, he, -, hy | ⟨i', g', -, hi'⟩⟩ := hf
      · cases he
        exact notX (hX.cluster.ref_present (List.mem_of_getElem? hi) hy).choose_spec
      · cases he
        exact notX (hX.cluster.ref_present (List.mem_of_getElem? hi')
          (by simp [ClusterBarrier.Record.refs])).choose_spec
    · cases op with
      | arrive => simp at hm
      | wait =>
        obtain ⟨y, hy, hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨rc, hrc, hyr⟩ := List.mem_flatMap.mp hy
        unfold needsIf at hm
        split_ifs at hm
        · obtain rfl := Need.node.inj (List.mem_singleton.mp hm)
          cases hf
          exact notX (hX.cluster.ref_present hrc hyr).choose_spec
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
      exact notX hev
    · simp at hm
  all_goals simp [KindNeeds] at hmem

/-- The issue of a new collective only reaches its own return and blocked peer returns. -/
theorem snoc_tccoll_from_issue (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hc : isTcColl e = true) {v : Ref × Bool}
    (h : Waits L (X.snoc g e r) (.thread (X.newId g), false) v) : TcSink L X g v := by
  obtain ⟨t, ht⟩ := TcCollective.kind_of_coll hc
  have hs := asyncSilent_of_tcColl hc
  have hord : e.kind.Ordinary := by rw [ht]; trivial
  have hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok := by
    intros; rw [ht]; simp
  have noOld : ∀ w, ¬ Waits L X (.thread (X.newId g), false) w := by
    intro w hw
    obtain ⟨ev, he⟩ := (waits_present hX.effectValidity hw).1
    have hl := len_of_get he
    simp at hl
  obtain ⟨v, b'⟩ := v
  rcases h with ⟨heq, -, hb', _⟩ | ⟨hb, _⟩ | ⟨i, j, hi, hj, hbar⟩ |
    ⟨_, _, i, j, hi, _, _, n, his, _⟩ |
    ⟨_, h2, i, j, hi, hj, hwarp, k, hit, hjt⟩ | ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨i, j, hi, hj, hcl⟩ |
    ⟨_, h2, j, hj, hw⟩ | ⟨h1, h2, i, j, hi, hj, hw⟩ | ⟨hb, _⟩ | ⟨i, j, hi, hj, hw⟩ |
    ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨_, _, hi⟩
  · exact .inl (Prod.ext heq.symm hb')
  · cases hb
  · cases hi
    obtain ⟨ev, he⟩ := (ctaWaits_snoc_old hX.ctaBar hbar).1
    have hl := len_of_get he; simp at hl
  · cases hi
    have hl := ((snoc_shflK hns).mp his).1; simp at hl
  · cases hi
    subst hj
    subst h2
    rw [snoc_tcK_new hit] at hjt
    rcases snoc_index_cases hjt.lt with hjold | hjnew
    · exact .inr ⟨j, rfl, hjold, hwarp, (snoc_tcK_of_old hjold).mp hjt⟩
    · rw [hjnew]; exact .inl rfl
  · cases hb
  · cases hb
  · cases hi
    obtain ⟨ev, he⟩ := (clusterWaits_snoc_old hX.cluster hcl).1
    have hl := len_of_get he; simp at hl
  · subst hj
    subst h2
    rcases snoc_tc_witness hX hg ht hw with rfl | ⟨-, hsink⟩
    · exact .inl rfl
    · exact hsink
  · exact (noOld (v, b') (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1, h2, i, j, hi, hj, (snoc_warpWaits hord).mp hw⟩))))))))))).elim
  · cases hb
  · exact (noOld (v, b') (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨i, j, hi, hj, (snoc_regWaits hord).mp hw⟩))))))))))))).elim
  · cases hb
  · cases hb
  · obtain ⟨-, -, i, p, he, -, -, hap, -⟩ := hi
    have hl := refPresent_issuer_lt hX.effectValidity (f := .async _ p)
      ((hs.snoc_asyncPresent).mp hap)
    rw [← Ref.thread.inj he] at hl
    exact absurd hl (lt_irrefl _)

/-- **Appending a warp-collective tensor-core instruction is a sink frame** for its two nodes
and the returns of the warp's lanes blocked at the same instance. -/
theorem snoc_tccoll_sinkFrame (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hc : isTcColl e = true) :
    SinkFrame L K A X (X.snoc g e r)
      (fun x => x.1 = .thread (X.newId g) ∨ TcSink L X g x) := by
  obtain ⟨t, ht⟩ := TcCollective.kind_of_coll hc
  have hs := asyncSilent_of_tcColl hc
  have hord : e.kind.Ordinary := by rw [ht]; trivial
  have sinkTrue : ∀ {v : Ref × Bool}, TcSink L X g v → v.2 = true := by
    rintro v (rfl | ⟨f, rfl, -⟩) <;> rfl
  refine snoc_sinkFrame (records := X.objects) hX (fun _ h => .inl h) ?_ SnocRecords.same
    (fun _ _ => (hs.snoc_asyncPresent).mp)
    (baseCausality_snocHistory_ordinary hX SnocRecords.same hord)
    ⟨fun x => if x.2 then 1 else 0, ?_⟩
  · rintro i (h | h)
    · exact Ref.thread.inj h
    · cases sinkTrue h
  · rintro ⟨u, b⟩ v h hu
    by_cases hsk : TcSink L X g (u, b)
    · exact (tcSink_sink hX hg hc hsk h).elim
    have hu' : u = .thread (X.newId g) := hu.resolve_right hsk
    subst hu'
    cases b with
    | true => exact (hsk (.inl rfl)).elim
    | false =>
      have hv := snoc_tccoll_from_issue hX hg hc h
      exact ⟨.inr hv, by simp [sinkTrue hv]⟩

end
end
end PTX
end
