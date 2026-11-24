-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocSinkFrame
public import Lemmas.Snoc.SnocExit
public import Lemmas.Snoc.AllocReturnSink

@[expose] public section

/-! Execution-order preservation for an ordinary source instruction. In addition to the
instruction's own stage edge, an allocation result store witnesses its participants' returns. -/
namespace PTX
open AsyncCopy
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- An ordinary append can only witness another event by publishing a nonleader allocation
result. All other witnesses are from existing histories, events of the collective's kind, or
exits that precede the collective. -/
theorem snoc_new_witness_allocResult (hX : Consistent L K A mem0 X) (hk : e.kind.WaitFree)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hx : e.kind = .exit → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false) {j : EvId} :
    Witness L (X.snoc g e r) (.thread (X.newId g)) j →
      laneOf L j.1 ≠ 0 ∧ Tmem.Pair.AllocResultFill L (X.snoc g e r) j (.thread (X.newId g)) := by
  rintro ⟨fills, hmem, -, hf⟩
  by_contra hresult
  have hnone : X.get (X.newId g) = none := List.getElem?_eq_none (le_refl _)
  have notX : ∀ {ev}, X.get (X.newId g) = some ev → False := fun h => by
    rw [hnone] at h; cases h
  have kindNew : ∀ {pc k}, (X.snoc g e r).get (X.newId g) = some ⟨pc, k⟩ → e.kind = k :=
    fun h => by rw [snoc_get_new] at h; rw [Option.some.inj h]
  have mapped : ∀ {α : Type} (l : List α) (P : α → Ref → Prop),
      Need.node fills ∈ l.map (fun a => Need.node (P a)) → ∃ a ∈ l, fills = P a := by
    intro α l P hm
    obtain ⟨a, ha', he⟩ := List.mem_map.mp hm
    exact ⟨a, ha', (Need.node.inj he).symm⟩
  have hord := hk.ordinary
  have oldReady : ∀ {pc k}, (X.snoc g e r).get j = some ⟨pc, k⟩ → e.kind ≠ k →
      k.resume = .blocking true → X.get j = some ⟨pc, k⟩ ∧ Ready L X j := by
    intro pc k hg hne hres
    have hj : X.get j = some ⟨pc, k⟩ := snoc_get_not_kind hg hne
    refine ⟨hj, hX.dependency.ready j ?_⟩
    unfold Returned
    rw [hj]
    cases k <;> simp_all [Kind.resume]
  have takeOld : ∀ {pc k}, X.get j = some ⟨pc, k⟩ →
      ((X.snoc g e r).tr j.1).take j.2 = (X.tr j.1).take j.2 :=
    fun hj => snoc_take (len_of_get hj).le
  have newTake : ((X.snoc g e r).tr g).take (X.tr g).length = X.tr g := by
    rw [snoc_tr, ite_eq_left rfl, List.take_left']
    rfl
  have maskCase : ∀ {Q V : Type} (c : Kind → Option (WarpPart Q V)) {pc0 : Nat} {k0 : Kind},
      (X.snoc g e r).get j = some ⟨pc0, k0⟩ → c e.kind = none → c .exit = none →
      KindNeeds L X k0 j = maskNeeds L c X j → k0.resume = .blocking true →
      Need.node fills ∈ maskNeeds L c (X.snoc g e r) j → False := by
    intro Q V c pc0 k0 hgj hc hce hkn hres hm
    unfold maskNeeds at hm
    rw [hgj] at hm
    cases hcj : c k0 with
    | none => simp [hcj] at hm
    | some p =>
      simp only [Option.bind_some, hcj] at hm
      obtain ⟨l, hl, rfl⟩ := mapped _ _ hm
      obtain ⟨j', he, -, m, n, q, hat, ⟨⟨⟨ev, p', hg, hc', -⟩, -⟩, -⟩ | ⟨-, ⟨pc, hg⟩, hcnt⟩⟩ := hf
      · cases he
        rw [snoc_get_new] at hg
        cases Option.some.inj hg
        rw [hc] at hc'
        cases hc'
      · obtain ⟨hgl, hjl⟩ := Prod.ext_iff.mp (Ref.thread.inj he)
        simp only at hgl hjl
        subst hjl
        rw [← hgl] at hg hcnt
        have hexit : e.kind = .exit := kindNew hg
        have hk0e : e.kind ≠ k0 := by
          intro h
          rw [h, hcj] at hc
          cases hc
        obtain ⟨hjX, hrX⟩ := oldReady hgj hk0e hres
        have hpm : p.mask = m := by
          obtain ⟨⟨ev', p'', hg', hc'', hm'⟩, -⟩ := hat.1
          rw [hgj] at hg'
          cases hg'
          rw [hcj] at hc''
          cases hc''
          exact hm'
        have hatX : X.MaskAt c j m n q := by
          refine ⟨Execution.maskK_of_le le_snoc hjX hat.1, ?_⟩
          obtain ⟨ev', p'', h1, h2, h3⟩ := hat.2
          rw [hgj] at h1
          cases h1
          exact ⟨_, p'', hjX, h2, h3⟩
        obtain ⟨hl32, hlb⟩ := List.mem_filter.mp hl
        obtain ⟨j'', hj''⟩ := maskK_lane_of_ready (L := L) c (hx hexit) hjX hcj
          (fun n hn => by simp only [Needs, hjX]; rw [hkn]; exact hn) hrX hatX
          (List.mem_range.mp hl32) (by rw [← hpm]; simpa using hlb) hgl.symm
        have hlt := lt_countP_of_maskK hj''
        simp only at hcnt hlt
        rw [newTake] at hcnt
        omega
  have tcCase : Need.node fills ∈ tcNeeds L (X.snoc g e r) j → False := by
    intro hm
    obtain ⟨l, -, rfl⟩ := mapped _ _ (by unfold tcNeeds at hm; exact hm)
    obtain ⟨j', he, ⟨ev, hg, hc⟩, -⟩ := hf
    cases he
    rw [snoc_get_new] at hg
    cases Option.some.inj hg
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp [isTcColl] at hc
    all_goals exact hk.notTc _ rfl
  unfold Needs at hmem
  cases hget : (X.snoc g e r).get j with
  | none => simp [hget] at hmem
  | some ev =>
  simp only [hget] at hmem
  obtain ⟨pc, kd⟩ := ev
  cases kd
  case shfl =>
    refine maskCase shflClass hget ?_ rfl rfl rfl hmem
    cases h : e.kind <;> try rfl
    exact absurd h (hns _ _ _ _ _ _)
  case vote =>
    refine maskCase voteClass hget ?_ rfl rfl rfl hmem
    cases h : e.kind <;> try rfl
    all_goals (rw [h] at hlv; cases hlv)
  case voteMode =>
    refine maskCase voteClass hget ?_ rfl rfl rfl hmem
    cases h : e.kind <;> try rfl
    all_goals (rw [h] at hlv; cases hlv)
  case redux =>
    refine maskCase reduxClass hget ?_ rfl rfl rfl hmem
    cases h : e.kind <;> try rfl
    all_goals (rw [h] at hlv; cases hlv)
  case match_ =>
    refine maskCase matchClass hget ?_ rfl rfl rfl hmem
    cases h : e.kind <;> try rfl
    all_goals (rw [h] at hlv; cases hlv)
  case elect mask inst leader =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', pc', ld, he, hg⟩ := hf
    cases he
    have := kindNew hg
    rw [this] at hord
    exact hord
  case warpBar mask inst =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, pc', hg⟩ := hf
    cases he
    have := kindNew hg
    rw [this] at hord
    exact hord
  case matrix op own recv =>
    obtain ⟨l, hl, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, ⟨⟨ev, hg, hm⟩, -⟩ | ⟨⟨pc', hg⟩, hcnt⟩⟩ := hf
    · cases he
      rw [snoc_get_new] at hg
      cases Option.some.inj hg
      rw [hmat] at hm
      cases hm
    · obtain ⟨hgl, hjl⟩ := Prod.ext_iff.mp (Ref.thread.inj he)
      simp only at hgl hjl
      subst hjl
      rw [← hgl] at hg hcnt
      have hexit : e.kind = .exit := kindNew hg
      obtain ⟨hjX, hrX⟩ := oldReady hget (by rw [hexit]; intro h; cases h) rfl
      have hmemX : Need.node (fun x => ∃ j', x = .thread (warpLane L j.1 l, j') ∧
          (X.MatrixK (warpLane L j.1 l, j') (((X.tr j.1).take j.2).countP isMatrix) ∨
            X.ExitedShort isMatrix (warpLane L j.1 l, j')
              (((X.tr j.1).take j.2).countP isMatrix))) ∈ Needs L X j := by
        simp only [Needs, hjX, KindNeeds]
        exact List.mem_map.mpr ⟨l, hl, rfl⟩
      obtain ⟨x, -, j'', rfl, hmk | ⟨⟨pc'', hge⟩, -⟩⟩ := hrX _ hmemX
      · have hlt := lt_countP_of_matrixK hmk
        rw [takeOld hjX] at hcnt
        rw [← hgl] at hlt
        have hcount : ((X.snoc g e r).tr g).countP isMatrix = (X.tr g).countP isMatrix := by
          rw [snoc_tr, ite_eq_left rfl, List.countP_append]
          obtain ⟨pce, kde⟩ := e
          simp only at hexit
          subst hexit
          simp [isMatrix]
        simp only at hcnt hlt
        omega
      · rw [← hgl] at hge
        exact hx hexit j'' pc'' hge
  case setMaxReg inc n inst =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, -, -, pc', inc', n', ei, fi, -, hg⟩ := hf
    cases he
    have := kindNew hg
    rw [this] at hord
    exact hord
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
  case tc t =>
    cases t
    case ld => exact tcCase hmem
    case st => exact tcCase hmem
    case waitLd => exact tcCase hmem
    case waitSt => exact tcCase hmem
    case resource group dst request =>
      simp only [KindNeeds, resourceNeeds] at hmem
      rcases List.mem_append.mp hmem with hcore | halloc
      · rcases List.mem_append.mp hcore with hm | hm
        · exact tcCase hm
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
      · have hn : laneOf L j.1 ≠ 0 := by
          intro hl
          cases request <;> simp [Tmem.Pair.allocResultNeeds, hl] at halloc
        cases Tmem.Pair.allocResultNeeds_node L halloc
        exact hresult ⟨hn, hf⟩
    all_goals simp [KindNeeds] at hmem
  all_goals simp [KindNeeds] at hmem

/-- An instruction other than a write cannot publish an allocation result. -/
theorem snoc_not_allocResult_of_not_wr (hwr : ∀ a bs, e.kind ≠ .wr a bs) (j : EvId) :
    ¬ Tmem.Pair.AllocResultFill L (X.snoc g e r) j (.thread (X.newId g)) := by
  intro h
  obtain ⟨store, _, _, _, heq, hwrite⟩ := Tmem.Pair.AllocResultFill.written L h
  cases heq
  rw [snoc_get_new] at hwrite
  exact hwr _ _ (congrArg Event.kind (Option.some.inj hwrite))

/-- An ordinary append with no allocation result supplies no new witness. -/
theorem snoc_new_not_witness (hX : Consistent L K A mem0 X) (hk : e.kind.WaitFree)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hx : e.kind = .exit → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false) {j : EvId}
    (hpublish : ¬ Tmem.Pair.AllocResultFill L (X.snoc g e r) j (.thread (X.newId g))) :
    ¬ Witness L (X.snoc g e r) (.thread (X.newId g)) j :=
  fun h => hpublish (snoc_new_witness_allocResult hX hk hns hx hlv hmat h).2

/-- A plain source instruction only orders its own completion and any nonleader allocation
returns for which it publishes the result. -/
theorem snoc_plain_edges_from_new (hX : Consistent L K A mem0 X)
    (hk : e.kind.WaitFree)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hx : e.kind = .exit → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hrmw : ∀ a old new, e.kind = .rmw a old new → a.release = false)
    {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.snoc g e r) (.thread (g,(X.tr g).length),b) v) :
    b = false ∧ (v = (.thread (X.newId g),true) ∨ ∃ j, v = (.thread j,true) ∧
      laneOf L j.1 ≠ 0 ∧ Tmem.Pair.AllocResultFill L (X.snoc g e r) j (.thread (X.newId g))) := by
  have hord := hk.ordinary
  have hwr : ∀ a bs, e.kind = .wr a bs → a.release = false := by
    intro a bs he; rw [he] at hord; exact hord
  have hsc : ∀ s, e.kind ≠ .fence .sc s := by
    intro s he; rw [he] at hord; exact hord
  have noBase : ∀ {f : EvId}, ¬ baseCausality L (X.snoc g e r) (g, (X.tr g).length) f :=
    snoc_no_baseCausality_from_new_of_not_arrive hna hwr hrmw hsc
  have noOld : ¬ Waits L X (.thread (g,(X.tr g).length),b) v := by
    intro hw
    obtain ⟨ev,he⟩ := (waits_present hX.effectValidity hw).1
    have hl := len_of_get he
    simp at hl
  rcases h with ⟨heq,hb,hb',_⟩ | ⟨_,_,i,j,hi,_,hij,hs,hl⟩ |
    ⟨i,j,hi,hj,hbar⟩ | ⟨_,_,i,j,hi,_,_,n,his,_⟩ |
    ⟨_,_,i,j,hi,_,_,k,hit,_⟩ | ⟨h1,h2,ha⟩ | ⟨h1,h2,m,ho⟩ |
    ⟨i,j,hi,hj,hcl⟩ | ⟨h1,h2,j,hj,hw⟩ | ⟨h1,h2,i,j,hi,hj,hw⟩ |
    ⟨h1,h2,i,j,hi,hj,hw⟩ | ⟨i,j,hi,hj,hw⟩ | ⟨h1,h2,i,j,hi,hj,cta,hp⟩ |
    ⟨h1,h2,i,j,hi,hj,hw⟩ | ⟨h1,h2,hi⟩
  · exact ⟨hb,.inl (Prod.ext heq.symm hb')⟩
  · cases hi
    rw [← hij,snoc_len,ite_eq_left rfl] at hl
    simp only at hs; omega
  · cases hi
    obtain ⟨ev,he⟩ := (ctaWaits_snoc_old hX.ctaBar hbar).1
    have hl := len_of_get he; simp at hl
  · cases hi
    have hl := ((snoc_shflK hns).mp his).1; simp at hl
  · cases hi
    have hl := ((snoc_tcK hk.notTc).mp hit).lt; simp at hl
  · rcases ha with ⟨-, hb0, -⟩ | ⟨-, -, hs⟩
    · rw [h1] at hb0; cases hb0
    · simp [StageEdge] at hs
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1,h2,m,ho⟩)))))))).elim
  · cases hi
    obtain ⟨ev,he⟩ := (clusterWaits_snoc_old hX.cluster hcl).1
    have hl := len_of_get he; simp at hl
  · exact ⟨h1, .inr ⟨j, Prod.ext hj h2, snoc_new_witness_allocResult hX hk hns hx hlv hmat hw⟩⟩
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1,h2,i,j,hi,hj,(snoc_warpWaits hord).mp hw⟩))))))))))).elim
  · cases hi
    exact (noBase (.single (.inr (.inr (.inr (.inr (.inr (.inl hw)))))))).elim
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨i,j,hi,hj,(snoc_regWaits hord).mp hw⟩))))))))))))).elim
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1,h2,i,j,hi,hj,cta,hp⟩)))))))))))))).elim
  · cases hi
    exact (noBase (.single (.inr (.inr (.inr (.inr (.inr (.inr hw)))))))).elim
  · obtain ⟨-, -, i, p, he, -, -, hap, -⟩ := hi
    have hl := refPresent_issuer_lt hX.effectValidity (f := .async _ p)
      ((snoc_asyncPresent_of_not_tc hk.notTc).mp hap)
    rw [← Ref.thread.inj he] at hl
    exact absurd hl (lt_irrefl _)

theorem snoc_plain_from_new (hX : Consistent L K A mem0 X)
    (hk : e.kind.WaitFree)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hx : e.kind = .exit → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hrmw : ∀ a old new, e.kind = .rmw a old new → a.release = false)
    (hpublish : ∀ j, ¬ Tmem.Pair.AllocResultFill L (X.snoc g e r) j (.thread (X.newId g)))
    {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.snoc g e r) (.thread (g,(X.tr g).length),b) v) :
    b = false ∧ v = (.thread (X.newId g),true) := by
  obtain ⟨hb, hv | ⟨j, _, _, hfill⟩⟩ :=
    snoc_plain_edges_from_new hX hk hns hx hlv hmat hna hrmw h
  · exact ⟨hb, hv⟩
  · exact (hpublish j hfill).elim

/-- Appending a plain source instruction is a sink frame for its two nodes. -/
theorem snoc_plain_sinkFrame (hX : Consistent L K A mem0 X)
    (hk : e.kind.WaitFree)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok) (hx : e.kind ≠ .exit)
    (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hrmw : ∀ a old new, e.kind = .rmw a old new → a.release = false)
    (hpublish : ∀ j, ¬ Tmem.Pair.AllocResultFill L (X.snoc g e r) j (.thread (X.newId g))) :
    SinkFrame L K A X (X.snoc g e r) (fun x => x.1 = .thread (X.newId g)) :=
  snoc_sinkFrame_new hX (fun _ _ => (snoc_asyncPresent_of_not_tc hk.notTc).mp)
    (baseCausality_snocHistory_ordinary (records := X.objects) hX SnocRecords.same hk.ordinary)
    (fun _ _ h => snoc_plain_from_new hX hk hns (fun h => absurd h hx) hlv hmat hna hrmw hpublish h)

/-- An allocation that obtains its result from the new store has not yet resumed. -/
private theorem snoc_alloc_recipient_terminal (hX : Consistent L K A mem0 X)
    (hk : e.kind.WaitFree) {i : EvId} (hn : laneOf L i.1 ≠ 0)
    (hf : Tmem.Pair.AllocResultFill L (X.snoc g e r) i (.thread (X.newId g))) :
    ∃ pc group dst count,
      (X.snoc g e r).get i = some ⟨pc, .tc (.resource group dst (.alloc count))⟩ ∧
      i.2 + 1 = ((X.snoc g e r).tr i.1).length := by
  obtain ⟨dst, hresult⟩ := hf
  have hresult' := hresult
  obtain ⟨_, hlead, _, _, _, pc, group, count, _, _, _, _, hi, _, _, _⟩ := hresult'
  have hne : i.1 ≠ g := by
    intro h
    exact hn (h ▸ hlead)
  have hiold := snoc_get_not_kind hi (by intro he; have ht := hk.notTc; simp [he] at ht)
  have hnReturned : ¬ Returned X i := by
    intro hr
    obtain ⟨old, _, hfill⟩ := hX.dependency.ready i hr _
      (allocResult_witnessed L X i hiold hn)
    cases old with
    | async j p => exact hfill.elim
    | thread old =>
      obtain ⟨loc, hold⟩ := hfill
      have hsame := Tmem.Pair.AllocResult.unique (hold.mono le_snoc) hresult
      obtain ⟨_, _, hget⟩ := hold.writes
      rw [hsame] at hget
      have hfresh : X.get (X.newId g) = none := List.getElem?_eq_none (le_refl _)
      rw [hfresh] at hget
      cases hget
  have hil := len_of_get hiold
  have hlast : i.2 + 1 = (X.tr i.1).length := by
    simp [Returned, hiold, Kind.resume, TcKind.resume] at hnReturned
    omega
  exact ⟨pc, group, some dst, count, hi, by rwa [snoc_len, ite_eq_right hne]⟩

/-- No unchanged synchronization history names the new event. -/
private theorem snoc_no_objectOrder (hX : Consistent L K A mem0 X)
    {o : OrderObject} {b : Bool} {v : Ref × Bool} :
    ¬ ObjectOrder L (X.snoc g e r) o (.thread (X.newId g), b) v := by
  intro he
  have hnone : X.get (X.newId g) = none := List.getElem?_eq_none (le_refl _)
  suffices hp : ∃ ev, X.get (X.newId g) = some ev by simp [hnone] at hp
  rcases v with ⟨v, b'⟩
  cases o with
  | mbar m =>
    obtain ⟨_, _, a, z, ra, rz, hra, hid, _⟩ := he
    have hp := object_record_present hX.tma (List.mem_of_getElem? hra)
    rw [hid] at hp
    exact hp
  | ctaBar c id =>
    obtain ⟨_, _, i, j, hi, hj, _, _, a, z, ra, rz, hra, hrz, haz, ha, hz, hia, hjz⟩ := he
    cases hi
    exact hX.ctaBar.ref_present (List.mem_of_getElem? hra) hia
  | cluster c =>
    obtain ⟨i, j, hi, hj, _, _, a, z, ra, rz, hra, hrz, haz, hia, hjz, _, _⟩ := he
    cases hi
    exact hX.cluster.ref_present (List.mem_of_getElem? hra) hia
  | tmem c =>
    obtain ⟨_, _, i, j, hi, hj, ht⟩ := he
    cases hi
    obtain ⟨pc, group, dst, req, hg⟩ := Tmem.Pair.Precedes.actual hX.tmemPair ht
    exact ⟨_, hg⟩

/-- The memory orders still have just the new instruction's own stage edge.
The dependency order may also reach a pending nonleader's allocation return. -/
theorem snoc_plain_orderOk (hX : Consistent L K A mem0 X)
    (hk : e.kind.WaitFree)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok) (hx : e.kind ≠ .exit)
    (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hrmw : ∀ a old new, e.kind = .rmw a old new → a.release = false) :
    OrderOk L K A (X.snoc g e r) := by
  let Y := X.snoc g e r
  let S : Ref × Bool → Prop := fun a => a.1 = .thread (X.newId g)
  let rank : Ref × Bool → Nat := fun a => if a.2 then 1 else 0
  have hstage : ∀ u v, stageCausality L Y u v → S u → S v ∧ rank u < rank v := by
    rintro ⟨u, b⟩ ⟨v, b'⟩ he (rfl : u = _)
    rcases he with (⟨hv, rfl, rfl, _⟩ | ⟨_, _, he⟩) |
      ⟨_, _, i, j, hi, _, hb⟩ | ⟨_, _, j, _, hcopy⟩
    · cases hv
      exact ⟨rfl, show 0 < 1 by decide⟩
    · cases v <;> cases he
    · cases hi
      exact (snoc_no_baseCausality_from_new_of_not_arrive hna
        (by intro a bs h; have h' := hk.ordinary; rw [h] at h'; exact h')
        hrmw (by intro s h; have h' := hk.ordinary; rw [h] at h'; exact h') hb).elim
    · obtain ⟨i, p, w, ws, he, _⟩ := hcopy
      cases he
  have ha : ThreadAppend X Y (· = X.newId g) := SnocRecords.threadAppend SnocRecords.same
  have ht : SinkFrame.Transport L K A X Y S :=
    ha.orderTransport hX (fun i b h => congrArg Ref.thread h)
      (fun i h => Ref.thread.inj h) (fun _ _ => (snoc_asyncPresent_of_not_tc hk.notTc).mp)
      (baseCausality_snocHistory_ordinary hX SnocRecords.same hk.ordinary)
      (fun u v he hv hu => hv (hstage u v he hu).1)
  refine ht.orderOk_of_orders hX.orderOk rank hstage ?_ ?_ ?_ ?_
  · intro x w he hx
    change x = .thread (X.newId g) at hx
    subst x
    rcases he with ⟨_, j, m, pc, q, ws, us, gg, _, hw, hu, _⟩ |
      ⟨i, p, j, k, he, _⟩
    · rcases hu with ⟨i, m, tx, count, hi, _, pc', harr⟩ | ⟨i, he, _⟩
      · cases hi
        rw [snoc_get_new] at harr
        exact (hna _ _ _ _ (congrArg Event.kind (Option.some.inj harr))).elim
      · rcases he with he | he <;> cases he
    · cases he
  · rintro o ⟨u, b⟩ v he (rfl : u = _)
    apply False.elim
    apply snoc_no_objectOrder hX (o := o) (b := b) (v := v)
    cases o with
    | mbar => exact he.1
    | ctaBar | cluster | tmem => exact he
  · intro m i p y he
    refine ⟨fun h => ?_, fun h => by cases h⟩
    have hi := ha.async_issue_old hX he
    cases Ref.thread.inj h
    exact (lt_irrefl _) hi
  · intro o ho
    let D : Ref × Bool → Prop := fun v => S v ∨ ∃ i,
      v = (.thread i, true) ∧ laneOf L i.1 ≠ 0 ∧
      Tmem.Pair.AllocResultFill L Y i (.thread (X.newId g))
    apply SinkFrame.acyclic_direct (S := D) (rank := rank) _ _
      (hX.dependency.acyclic o ho)
    · rintro ⟨u, b⟩ v he (hu | ⟨i, hu, hn, hf⟩)
      · change u = _ at hu
        subst u
        obtain ⟨f, b'⟩ := v
        rcases he with (hs | hs | ⟨rfl, hb', j, hj, hw⟩ | ⟨_, _, w, j, hi, _, hr⟩) | ho'
        · have he := hstage (.thread (X.newId g), b) (f, b') (.inl hs) rfl
          exact ⟨.inl he.1, he.2⟩
        · obtain ⟨_, _, i, p, hi, _, _, hp, _⟩ := hs
          cases hi
          exact (lt_irrefl _ (refPresent_issuer_lt hX.effectValidity (f := .async (X.newId g) p)
            ((snoc_asyncPresent_of_not_tc hk.notTc).mp hp))).elim
        · have hj' : (f, b') = (.thread j, true) := Prod.ext hj hb'
          cases hj'
          obtain ⟨hn, hf⟩ :=
            snoc_new_witness_allocResult hX hk hns (fun h => absurd h hx) hlv hmat hw
          exact ⟨.inr ⟨j, rfl, hn, hf⟩, show 0 < 1 by decide⟩
        · cases hi
          obtain ⟨hj, hbefore, hbound⟩ := hr.1
          rw [← hj, snoc_len, ite_eq_left rfl] at hbound
          change (X.tr g).length < j.2 at hbefore
          omega
        · exact (snoc_no_objectOrder hX ho').elim
      · cases hu
        obtain ⟨pc, group, dst, count, hg, hl⟩ := snoc_alloc_recipient_terminal hX hk hn hf
        have hg' := snoc_get_not_kind hg (by intro he; have ht := hk.notTc; simp [he] at ht)
        obtain ⟨store, site, dst, bytes, hstore, hw⟩ := Tmem.Pair.AllocResultFill.written L hf
        cases hstore
        rw [snoc_get_new] at hw
        have hkt : e.kind.isTma = false := by
          rw [congrArg Event.kind (Option.some.inj hw)]
          rfl
        exact (snoc_alloc_return_dep_sink hX hkt hg' hl ho v he).elim
    · intro u v hu hv he
      have hsu : ¬ S u := fun h => hu (.inl h)
      have hsv : ¬ S v := fun h => hv (.inl h)
      rcases he with he | he
      · exact Relation.TransGen.mono (fun _ _ => Or.inl) _ _ (ht.dep u v hsu hsv he)
      · exact .single (.inr (ht.object o u v hsu hsv he))

/-- Appending an exit to a thread that has not exited is a sink frame for its two nodes. -/
theorem snoc_exit_sinkFrame (hX : Consistent L K A mem0 X) (he : e.kind = .exit)
    (hgx : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩) :
    SinkFrame L K A X (X.snoc g e r) (fun x => x.1 = .thread (X.newId g)) := by
  have hk : e.kind.WaitFree := .of_plain (by rw [he]; rfl)
  have hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok := by intros; rw [he]; simp
  have hmat : isMatrix e = false := by obtain ⟨pc, k⟩ := e; simp only at he; subst he; rfl
  exact snoc_sinkFrame_new hX (fun _ _ => (snoc_asyncPresent_of_not_tc hk.notTc).mp)
    (baseCausality_snocHistory_ordinary (records := X.objects) hX SnocRecords.same hk.ordinary)
    (fun _ _ h => snoc_plain_from_new hX hk hns (fun _ => hgx) (by rw [he]; rfl) hmat
      (by intros; rw [he]; simp) (by intros _ _ _ h; rw [he] at h; cases h)
      (snoc_not_allocResult_of_not_wr (by simp [he])) h)

/-- Appending an exit to a thread that has not exited keeps the execution-order axioms. -/
theorem snoc_exit_orderOk (hX : Consistent L K A mem0 X) (he : e.kind = .exit)
    (hgx : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩) : OrderOk L K A (X.snoc g e r) :=
  (snoc_exit_sinkFrame hX he hgx).orderOk hX.orderOk

end
end
end PTX
