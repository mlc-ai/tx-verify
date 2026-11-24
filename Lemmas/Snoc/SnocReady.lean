-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocSinkFrame

@[expose] public section

/-! Readiness (DEP-ORDER, `DependencyOk.ready`) after appending thread events. Every need of an
old event reads the event, the trace prefixes of old events and the histories the append keeps,
so a need that `X` fills stays filled. An old event that returns only in the append is the last
event of its thread in `X`, which returns once the appended event exists. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

/-- The need `n'` of `X` gives the need `n` of an extension: a node of `X` that fills `n'` fills
`n`, and the condition of `n'` implies that of `n`. -/
def NeedImp (X : Execution) : Need → Need → Prop
  | .node f', .node f => ∀ x, X.RefPresent x → f' x → f x
  | .cond p', .cond p => p' → p
  | _, _ => False

theorem NeedImp.refl (X : Execution) (n : Need) : NeedImp X n n := by
  cases n with
  | node f => exact fun _ _ h => h
  | cond p => exact id

theorem needImp_map {X : Execution} {α : Type} (l : List α) {P P' : α → Ref → Prop}
    (himp : ∀ a ∈ l, ∀ x, X.RefPresent x → P' a x → P a x) {n : Need}
    (hn : n ∈ l.map fun a => Need.node (P a)) :
    ∃ n' ∈ l.map (fun a => Need.node (P' a)), NeedImp X n' n := by
  obtain ⟨a, hl, rfl⟩ := List.mem_map.mp hn
  exact ⟨_, List.mem_map.mpr ⟨a, hl, rfl⟩, himp a hl⟩

namespace ThreadAppend
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X Y : Execution}
  {New : EvId → Prop}

theorem maskK_mono (ha : ThreadAppend X Y New) {Q V : Type} {c : Kind → Option (WarpPart Q V)}
    {v : EvId} {m n : Nat} (hv : v.2 < (X.tr v.1).length) (h : X.MaskK c v m n) :
    Y.MaskK c v m n := by
  obtain ⟨⟨ev, p, hg, hc, hm⟩, hn⟩ := h
  exact ⟨⟨ev, p, by rw [ha.get v (ha.not_new hv)]; exact hg, hc, hm⟩, by rwa [ha.take v hv]⟩

theorem maskAt_mono (ha : ThreadAppend X Y New) {Q V : Type} {c : Kind → Option (WarpPart Q V)}
    {v : EvId} {m n : Nat} {q : Q} (hv : v.2 < (X.tr v.1).length) (h : X.MaskAt c v m n q) :
    Y.MaskAt c v m n q := by
  obtain ⟨hk, ev, p, hg, hc, hq⟩ := h
  exact ⟨ha.maskK_mono hv hk, ev, p, by rw [ha.get v (ha.not_new hv)]; exact hg, hc, hq⟩

theorem maskWait_mono (ha : ThreadAppend X Y New) {Q V : Type} {c : Kind → Option (WarpPart Q V)}
    {u v : EvId} (hu : u.2 < (X.tr u.1).length) (hv : v.2 < (X.tr v.1).length)
    (h : MaskWait L c X u v) : MaskWait L c Y u v := by
  obtain ⟨hs, m, n, q, hf, he | ⟨hb, ⟨pc, hg⟩, hc⟩⟩ := h
  · exact ⟨hs, m, n, q, ha.maskAt_mono hv hf, .inl (ha.maskAt_mono hu he)⟩
  · exact ⟨hs, m, n, q, ha.maskAt_mono hv hf, .inr ⟨hb,
      ⟨pc, by rw [ha.get u (ha.not_new hu)]; exact hg⟩, by rwa [ha.take u hu]⟩⟩

theorem matrixK_mono (ha : ThreadAppend X Y New) {v : EvId} {n : Nat}
    (hv : v.2 < (X.tr v.1).length) (h : X.MatrixK v n) : Y.MatrixK v n := by
  obtain ⟨⟨ev, hg, hm⟩, hn⟩ := h
  exact ⟨⟨ev, by rw [ha.get v (ha.not_new hv)]; exact hg, hm⟩, by rwa [ha.take v hv]⟩

/-- A node present in `X` is present in the append. -/
theorem present_mono (ha : ThreadAppend X Y New)
    (hpres : ∀ i p, X.AsyncPresent i p → Y.AsyncPresent i p) {x : Ref} (hx : X.RefPresent x) :
    Y.RefPresent x := by
  cases x with
  | thread i =>
    obtain ⟨ev, hev⟩ := hx
    exact ⟨ev, by rw [ha.get i (ha.not_new (len_of_get hev))]; exact hev⟩
  | async i p => exact hpres i p hx

/-- Every need of an old event in the append is filled directly (a poll need, filled by the
observed update itself) or comes from a need of the event in `X` (`NeedImp`): its conditions read
the event, old trace prefixes and the histories the append keeps, and the nodes that fill it in
`X` fill it in the append. A thread that exited in `X` performs no further matrix event. -/
theorem need_of_old (ha : ThreadAppend X Y New) {j : EvId}
    (hexit : (∃ pc op own recv, X.get j = some ⟨pc, .matrix op own recv⟩) →
      ∀ v pc, X.get v = some ⟨pc, .exit⟩ → (Y.tr v.1).countP isMatrix ≤ (X.tr v.1).countP isMatrix)
    (hj : ¬ New j) {n : Need} (hn : n ∈ Needs L Y j) :
    (∃ x, Y.RefPresent x ∧ ∃ fills, n = .node fills ∧ fills x) ∨
      ∃ n' ∈ Needs L X j, NeedImp X n' n := by
  have hjo := ha.get j hj
  have threadOld : ∀ {x : Ref} {i : EvId}, X.RefPresent x → x = .thread i →
      i.2 < (X.tr i.1).length := by
    intro x i hx hxi; subst hxi; obtain ⟨ev, hev⟩ := hx; exact len_of_get hev
  have getMono : ∀ {i : EvId} {ev : Event}, X.get i = some ev → Y.get i = some ev := by
    intro i ev hg; rw [ha.get i (ha.not_new (len_of_get hg))]; exact hg
  unfold Needs at hn
  rw [hjo] at hn
  cases hget : X.get j with
  | none => simp [hget] at hn
  | some ev =>
  simp only [hget] at hn
  have hjlt : j.2 < (X.tr j.1).length := len_of_get hget
  have htake := ha.take j hjlt
  have toX : (∃ n' ∈ KindNeeds L X ev.kind j, NeedImp X n' n) →
      (∃ x, Y.RefPresent x ∧ ∃ fills, n = .node fills ∧ fills x) ∨
        ∃ n' ∈ Needs L X j, NeedImp X n' n := by
    rintro ⟨n', hm, hi⟩
    exact .inr ⟨n', by simp only [Needs, hget]; exact hm, hi⟩
  have same : n ∈ KindNeeds L X ev.kind j →
      (∃ x, Y.RefPresent x ∧ ∃ fills, n = .node fills ∧ fills x) ∨
        ∃ n' ∈ Needs L X j, NeedImp X n' n :=
    fun hm => toX ⟨n, hm, NeedImp.refl X n⟩
  have maskCase : ∀ {Q V : Type} (c : Kind → Option (WarpPart Q V)),
      n ∈ maskNeeds L c Y j → ∃ n' ∈ maskNeeds L c X j, NeedImp X n' n := by
    intro Q V c hm
    unfold maskNeeds at hm ⊢
    rw [hjo] at hm
    generalize ((X.get j).bind fun ev => c ev.kind) = o at hm ⊢
    cases o with
    | none => simp at hm
    | some p =>
      refine needImp_map _ (fun l _ x hx => ?_) hm
      rintro ⟨j', rfl, hw⟩
      exact ⟨j', rfl, ha.maskWait_mono (threadOld hx rfl) hjlt hw⟩
  have tcCase : n ∈ tcNeeds L Y j → ∃ n' ∈ tcNeeds L X j, NeedImp X n' n := by
    intro hm
    unfold tcNeeds at hm ⊢
    rw [htake] at hm
    refine needImp_map _ (fun l _ x hx => ?_) hm
    rintro ⟨j', rfl, hk⟩
    exact ⟨j', rfl, (ha.tcK (ha.not_new (threadOld hx rfl))).mpr hk⟩
  have groupCase : ∀ k : GroupWait, n ∈ groupNeeds Y j k → n ∈ groupNeeds X j k := by
    intro k hm
    unfold groupNeeds at hm ⊢
    obtain ⟨i, hi, hm⟩ := List.mem_flatMap.mp hm
    by_cases hw : GroupWaitsFor Y k (j.1, i) j
    · simp only [needsIf, hw, ite_true] at hm
      have hold : (j.1, i).2 < (X.tr (j.1, i).1).length := by
        have := List.mem_range.mp hi
        simp only
        omega
      have hst : GroupWaitStages Y (j.1, i) k = GroupWaitStages X (j.1, i) k := by
        unfold GroupWaitStages; rw [ha.get _ (ha.not_new hold)]
      rw [hst] at hm
      refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
      simp only [needsIf, ha.groupWaitsFor hj hw, ite_true]
      exact hm
    · simp [needsIf, hw] at hm
  obtain ⟨pc, k⟩ := ev
  cases k
  case shfl => exact toX <| maskCase shflClass hn
  case vote => exact toX <| maskCase voteClass hn
  case voteMode => exact toX <| maskCase voteClass hn
  case redux => exact toX <| maskCase reduxClass hn
  case match_ => exact toX <| maskCase matchClass hn
  case elect mask inst leader =>
    refine toX (needImp_map _ (fun l _ x hx => ?_) hn)
    rintro ⟨j', pc', ld, rfl, hg⟩
    exact ⟨j', pc', ld, rfl, getMono hg⟩
  case warpBar mask inst =>
    refine toX (needImp_map _ (fun l _ x hx => ?_) hn)
    rintro ⟨j', rfl, pc', hg⟩
    exact ⟨j', rfl, pc', getMono hg⟩
  case matrix op own recv =>
    simp only [KindNeeds, htake] at hn
    refine toX (needImp_map _ (fun l _ x hx => ?_) hn)
    rintro ⟨j', rfl, hk | ⟨⟨pc', hg⟩, hc⟩⟩
    · exact ⟨j', rfl, .inl (ha.matrixK_mono (threadOld hx rfl) hk)⟩
    · exact ⟨j', rfl, .inr ⟨⟨pc', getMono hg⟩,
        le_trans (hexit ⟨pc, op, own, recv, hget⟩ _ _ hg) hc⟩⟩
  case setMaxReg inc n' inst =>
    simp only [KindNeeds] at hn
    refine toX (needImp_map _ (fun l _ x hx => ?_) hn)
    rintro ⟨j', rfl, hs⟩
    exact ⟨j', rfl, (ha.sameRequest (L := L) hj (ha.not_new (threadOld hx rfl))).mpr hs⟩
  case bar id count mode =>
    simp only [KindNeeds, ctaBarNeeds, ctaBarWarpNeeds, CtaBarCounted, CtaBarDone, ha.barriers,
      ha.ctaBarK hj] at hn
    exact same hn
  case cluster op =>
    simp only [KindNeeds, clusterNeeds, clusterWarpNeeds, ClusterCounted, ha.clusters] at hn
    exact same hn
  case bulkWait mode rem => exact same (groupCase (.bulk mode) hn)
  case asyncWait rem => exact same (groupCase .cpAsync hn)
  case wait m q ok acq sc =>
    cases ok
    · simp [KindNeeds] at hn
    simp only [KindNeeds, ite_true, pollNeeds] at hn
    obtain ⟨r, -, hm⟩ := List.mem_flatMap.mp hn
    by_cases hob : MbarObserved Y r.id (.thread j)
    swap
    · simp [needsIf, hob] at hm
    simp only [needsIf, hob, ite_true, List.mem_singleton] at hm
    exact .inl ⟨r.id, hob.1, _, hm, rfl⟩
  case tc t =>
    cases t
    case ld => exact toX (tcCase hn)
    case st => exact toX (tcCase hn)
    case waitLd => exact toX (tcCase hn)
    case waitSt => exact toX (tcCase hn)
    case resource group dst request =>
      simp only [KindNeeds] at hn
      unfold resourceNeeds at hn
      rcases List.mem_append.mp hn with hn | hresult
      · rcases List.mem_append.mp hn with hm | hm
        · obtain ⟨n', h1, h2⟩ := tcCase hm
          refine toX ⟨n', ?_, h2⟩
          simp only [KindNeeds]
          unfold resourceNeeds
          exact List.mem_append_left _ (List.mem_append_left _ h1)
        have hMW : Tmem.Pair.MustWait Y j = Tmem.Pair.MustWait X j := by
          unfold Tmem.Pair.MustWait
          rw [hjo, ha.tmemPairBlocks]
        have hRR : ReuseRelease L Y j = ReuseRelease L X j := by
          funext j1
          unfold ReuseRelease
          rw [ha.tmemHistory]
        have hP : Tmem.Pair.Performed L Y j = Tmem.Pair.Performed L X j := by
          unfold Tmem.Pair.Performed; rw [ha.tmemHistory]
        have hC : Tmem.Pair.Covered L Y j = Tmem.Pair.Covered L X j := by
          unfold Tmem.Pair.Covered Tmem.Pair.Completed; rw [ha.tmemHistory, ha.tmemPairing]
        rw [hMW, hRR, hP, hC, ha.tmemHistory, ha.tmemPairing] at hm
        refine same ?_
        simp only [KindNeeds]
        unfold resourceNeeds
        exact List.mem_append_left _ (List.mem_append_right _ hm)
      · have hnode := Tmem.Pair.allocResultNeeds_transport (Y := X) L hresult
        obtain rfl := Tmem.Pair.allocResultNeeds_node L hresult
        apply toX
        refine ⟨Need.node (Tmem.Pair.AllocResultFill L X j), ?_,
          fun _ _ hf => hf.mono_trace ha.tracePrefix⟩
        exact List.mem_append_right _ hnode
    all_goals simp [KindNeeds] at hn
  all_goals simp [KindNeeds] at hn

end ThreadAppend

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {g : Nat} {e : Event} {r : Nat → Option Ref} {records : Loc → List (MBarrier.Record Ref)}

/-- A stage present in `X` stays present after an appended event. -/
theorem snoc_asyncPresent_old {i : EvId} {p : Part} (h : X.AsyncPresent i p) :
    (X.snoc g e r).AsyncPresent i p := by
  cases p <;> simp only [Execution.AsyncPresent, snoc_async] at h ⊢
  all_goals try exact h
  case mmaRead isB index =>
    obtain ⟨l, b, hf, ho⟩ := h
    refine ⟨l, b, ?_, ho⟩
    rcases hf with ⟨d, s, ac, mk, ⟨pc, hi⟩, hl⟩ | ⟨c, k, cta, ⟨pc, hi⟩, rest⟩
    · exact .inl ⟨d, s, ac, mk, ⟨pc, Execution.le_get le_snoc hi⟩, hl⟩
    · exact .inr ⟨c, k, cta, ⟨pc, Execution.le_get le_snoc hi⟩, rest⟩

/-- The last event of thread `g`, if it returns once a next event of its thread exists (a CTA or
cluster barrier, a group wait, a register request or a warp-collective `tcgen05` event), is
ready: the thread may perform its next event. -/
def LastReady (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ pc k, X.get (g, (X.tr g).length - 1) = some ⟨pc, k⟩ → k.resume = .blocking false →
    Ready L X (g, (X.tr g).length - 1)

/-- An old event that `X` holds ready stays ready after an appended event of thread `g`; for a
matrix event, when `g` has not exited or the appended event is no matrix event. -/
theorem ready_snocHistory_old (hrec : SnocRecords X g records) {j : EvId}
    (hexit : (∃ pc op own recv, X.get j = some ⟨pc, .matrix op own recv⟩) →
      isMatrix e = true → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hj : j ≠ X.newId g) (hr : Ready L X j) : Ready L (X.snocHistory g e r records) j := by
  have ha := hrec.threadAppend (e := e) (r := r)
  have hpres : ∀ i p, X.AsyncPresent i p → (X.snocHistory g e r records).AsyncPresent i p :=
    fun i p h => snoc_asyncPresent_old (g := g) (e := e) (r := r) h
  have hex : (∃ pc op own recv, X.get j = some ⟨pc, .matrix op own recv⟩) →
      ∀ v pc, X.get v = some ⟨pc, .exit⟩ →
      ((X.snocHistory g e r records).tr v.1).countP isMatrix ≤ (X.tr v.1).countP isMatrix := by
    intro hm v pc hv
    change ((X.snoc g e r).tr v.1).countP isMatrix ≤ _
    rw [snoc_tr]
    split_ifs with hvg
    · subst hvg
      cases hme : isMatrix e
      · simp [hme]
      · exact absurd hv (hexit hm hme v.2 pc)
    · exact le_refl _
  intro n hn
  rcases ha.need_of_old hex hj hn with ⟨x, hx, fills, rfl, hf⟩ | ⟨n', hn', himp⟩
  · exact ⟨x, hx, hf⟩
  · have h' := hr n' hn'
    cases n' <;> cases n <;> simp only [NeedImp] at himp
    · obtain ⟨x, hx, hf⟩ := h'
      exact ⟨x, ha.present_mono hpres hx, himp x hx hf⟩
    · exact himp h'

/-- **Readiness after appending one event of thread `g`** whose histories only gain records of
the appended event: old events keep their readiness (`ThreadAppend.need_of_old`), the previous
last event of the thread is ready (`LastReady`), and the appended event is ready if it has
returned. A matrix event is appended only to a thread that has not exited. -/
theorem ready_snocHistory (hX : Consistent L K A mem0 X) (hrec : SnocRecords X g records)
    (hexit : isMatrix e = true → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlast : LastReady L X g)
    (hnew : Returned (X.snocHistory g e r records) (X.newId g) →
      Ready L (X.snocHistory g e r records) (X.newId g)) :
    ∀ j, Returned (X.snocHistory g e r records) j → Ready L (X.snocHistory g e r records) j := by
  have ha := hrec.threadAppend (e := e) (r := r)
  have mono : ∀ j, j ≠ X.newId g → Ready L X j → Ready L (X.snocHistory g e r records) j :=
    fun j hj hr => ready_snocHistory_old hrec (fun _ => hexit) hj hr
  intro j hr
  by_cases hjn : j = X.newId g
  · subst hjn; exact hnew hr
  refine mono j hjn ?_
  by_cases hrX : Returned X j
  · exact hX.dependency.ready j hrX
  have hjo := ha.get j hjn
  unfold Returned at hr hrX
  rw [hjo] at hr
  cases hget : X.get j with
  | none => simp [hget] at hr
  | some ev =>
  obtain ⟨pc, k⟩ := ev
  simp only [hget] at hr hrX
  have hjold : j.2 < (X.tr j.1).length := len_of_get hget
  have finish : j.2 + 1 < ((X.snocHistory g e r records).tr j.1).length →
      ¬ j.2 + 1 < (X.tr j.1).length → k.resume = .blocking false → Ready L X j := by
    intro h1 h2 hres
    change j.2 + 1 < ((X.snoc g e r).tr j.1).length at h1
    rw [snoc_len] at h1
    split_ifs at h1 with hjg
    · obtain ⟨j1, j2⟩ := j
      simp only at hjg h1 h2 hjold hget
      subst hjg
      have hj2 : j2 = (X.tr j1).length - 1 := by omega
      subst hj2
      exact hlast pc k hget hres
    · exact absurd h1 h2
  split at hr
  · rename_i heq
    cases heq
    simp only at hrX
    exact absurd hr hrX
  · rename_i ev hnw heq
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

end
end
end PTX
