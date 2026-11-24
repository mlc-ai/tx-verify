-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitingClosure
public import Lemmas.Execution.NeedFills
public import Lemmas.Snoc.ObjectAppend

@[expose] public section

/-! # Appending a completion stage

An extension that adds a stage of an asynchronous operation (a store's completion flag, a
notification, an MMA completion) is not a sink of the joint wait relation: a group wait that
covers the operation and has not returned gets a witness edge from the new stage to its return
(`Witness`, DEP-ORDER). Such a wait is pending: by `DependencyOk.ready` a returned wait has every
stage it needs, and the new stage was absent. A pending `cp.async.bulk.wait_group` or
`cp.async.wait_group` is the last event of its thread (`last_of_not_returned_bulkWait`), so its
return has no outgoing `Waits` edge (`groupWait_return_not_waits`) and it starts no base causality
edge (`groupWait_last_not_baseCausality`). The frame `sinkFrame_completion` therefore takes as `S`
the new stages together with the returns of the waits they witness. -/
namespace PTX
open AsyncCopy
noncomputable section

variable {L : Launch}

/-- A group wait event of `X`: a `cp.async.bulk.wait_group` or a `cp.async.wait_group`. -/
def GroupWaitEvent (X : Execution) (w : EvId) : Prop :=
  ∃ pc, (∃ mode rem, X.get w = some ⟨pc, .bulkWait mode rem⟩) ∨
    ∃ rem, X.get w = some ⟨pc, .asyncWait rem⟩

/-- The waiting event of a group wait is a group wait event. -/
theorem GroupWaitEvent.of_groupWaitsFor {X : Execution} {k : GroupWait} {i w : EvId}
    (h : GroupWaitsFor X k i w) : GroupWaitEvent X w := by
  cases k with
  | bulk mode =>
    obtain ⟨pc, rem, hg, -⟩ := h
    exact ⟨pc, .inl ⟨mode, rem, hg⟩⟩
  | cpAsync =>
    obtain ⟨pc, rem, hg, -⟩ := h
    exact ⟨pc, .inr ⟨rem, hg⟩⟩

/-- A group wait that has not returned is the last event of its thread. -/
theorem GroupWaitEvent.last {X : Execution} {w : EvId} (hw : GroupWaitEvent X w)
    (hr : ¬ Returned X w) : (X.tr w.1).length ≤ w.2 + 1 := by
  obtain ⟨pc, ⟨mode, rem, hg⟩ | ⟨rem, hg⟩⟩ := hw
  · exact last_of_not_returned_bulkWait hg hr
  · unfold Returned at hr
    simp only [hg, Kind.resume] at hr
    omega

/-- A group wait is recorded in no mbarrier history. -/
theorem GroupWaitEvent.not_record {X : Execution} {w : EvId} (hw : GroupWaitEvent X w)
    (ho : ObjectsOk X) {m : Loc} {r : MBarrier.Record Ref} (hr : r ∈ X.objects m) :
    r.id ≠ .thread w := by
  intro hid
  have ha := ((ho m).2.1 r hr).1
  rw [hid] at ha
  obtain ⟨pc, ⟨mode, rem, hg⟩ | ⟨rem, hg⟩⟩ := hw <;> simp [objectAction, hg] at ha

/-- A group wait is the source of no cluster barrier record. -/
theorem GroupWaitEvent.not_cluster {X : Execution} {w : EvId} (hw : GroupWaitEvent X w)
    (hc : ClusterHistoryOk L X) {c : Nat} {r : ClusterBarrier.Record EvId}
    (hr : r ∈ X.clusters c) : w ∉ r.refs := by
  intro hm
  by_cases hcl : c < L.nclusters
  · have hs := (hc.2.2 c hcl).2.1 r hr
    obtain ⟨pc, ⟨mode, rem, hg⟩ | ⟨rem, hg⟩⟩ := hw
    all_goals
      cases r with
      | exit g e =>
        simp only [ClusterBarrier.Record.refs, List.mem_singleton] at hm
        subst hm
        obtain ⟨-, -, pc', hg'⟩ := hs
        rw [hg] at hg'
        cases hg'
      | arrival a b release lanes =>
        simp only [ClusterBarrier.Record.refs, List.mem_map] at hm
        obtain ⟨p, hp, rfl⟩ := hm
        obtain ⟨-, -, pc', al, hg'⟩ := hs p hp
        rw [hg] at hg'
        cases hg'
      | wait a b lanes =>
        simp only [ClusterBarrier.Record.refs, List.mem_map] at hm
        obtain ⟨p, hp, rfl⟩ := hm
        obtain ⟨-, -, pc', al, hg'⟩ := hs p hp
        rw [hg] at hg'
        cases hg'
  · rw [hc.2.1 c (by omega)] at hr
    simp at hr

/-- A group wait is a lane of no Tensor Memory allocator request. -/
theorem GroupWaitEvent.not_participates {X : Execution} {w : EvId} (hw : GroupWaitEvent X w)
    (ht : Tmem.Pair.HistoriesOk L X) {cta : Nat} {x : Tmem.Pair.Requests}
    (hx : x ∈ X.tmemHistory cta) : ¬ Tmem.Pair.Participates L x.own w := by
  rintro ⟨lane, rfl⟩
  have hv := ((ht.1 cta).1 x hx).2.2.2.2.1 lane
  obtain ⟨pc, ⟨mode, rem, hg⟩ | ⟨rem, hg⟩⟩ := hw <;> rw [hg] at hv <;> cases hv

/-- The return of a group wait that is the last event of its thread, recorded in no object, cluster
barrier or allocator history, has no outgoing `Waits` edge. -/
theorem groupWait_return_not_waits {X : Execution} {w : EvId} (hw : GroupWaitEvent X w)
    (hlast : (X.tr w.1).length ≤ w.2 + 1)
    (hobj : ∀ m r, r ∈ X.objects m → r.id ≠ .thread w)
    (hcl : ∀ c r, r ∈ X.clusters c → w ∉ r.refs)
    (htm : ∀ cta x, x ∈ X.tmemHistory cta → ¬ Tmem.Pair.Participates L x.own w)
    (v : Ref × Bool) : ¬ Waits L X (.thread w, true) v := by
  obtain ⟨f, b'⟩ := v
  obtain ⟨pc, hg⟩ := hw
  intro h
  rcases h with ⟨-, h, -⟩ | ⟨-, -, i, j, hi, hj, h1, h2, h3⟩ |
    ⟨i, j, hi, hj, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
    ⟨-, -, h⟩ | ⟨-, -, m, h⟩ | ⟨i, j, hi, hj, h⟩ |
    ⟨h, -⟩ | ⟨h, -⟩ |
    ⟨-, -, i, j, hi, hj, h⟩ | ⟨i, j, hi, hj, h⟩ | ⟨-, -, i, j, hi, hj, cta, h⟩ |
    ⟨-, -, i, j, hi, hj, h⟩ | ⟨h, -⟩
  · cases h
  · cases hi
    rw [h1] at hlast
    omega
  · cases hi
    obtain ⟨-, -, h⟩ := h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  · cases h
  · cases h
  · rcases h with ⟨-, h, -⟩ | ⟨-, -, h⟩
    · cases h
    · exact h.elim
  · obtain ⟨a, b, r, s, ha, hid, -⟩ := h
    exact hobj m r (List.mem_of_getElem? ha) hid
  · cases hi
    obtain ⟨-, -, h⟩ := h
    rcases h with ⟨c, a, b, r, q, ha, -, -, hm, -, hb, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact hcl c r (List.mem_of_getElem? ha) hm
    all_goals cases h
  · cases h
  · cases h
  · cases hi
    obtain ⟨a, b, bs, cs, hwr, -⟩ := h
    rcases hwr with ⟨pc', hg'⟩ | ⟨old, pc', hg'⟩ <;>
      rcases hg with ⟨mode, rem, hg⟩ | ⟨rem, hg⟩ <;> rw [hg] at hg' <;> cases hg'
  · cases hi
    obtain ⟨h, -⟩ := h
    cases h
  · cases hi
    obtain ⟨k, l, x, y, hx, -, -, hp, -⟩ := h
    exact htm cta x (List.mem_of_getElem? hx) hp
  · cases hi
    rcases h with ⟨w', r, a, b, bs, cs, se, sf, hwr, -, -, hh, -⟩ | ⟨⟨s, s', ⟨pc', hg'⟩, -⟩, -⟩
    · rcases hh with ⟨rfl, -⟩ | ⟨sem, ⟨pc', hg'⟩, -⟩
      · rcases hwr with ⟨pc', hg'⟩ | ⟨old, pc', hg'⟩ <;>
          rcases hg with ⟨mode, rem, hg⟩ | ⟨rem, hg⟩ <;> rw [hg] at hg' <;> cases hg'
      · rcases hg with ⟨mode, rem, hg⟩ | ⟨rem, hg⟩ <;> rw [hg] at hg' <;> cases hg'
    · rcases hg with ⟨mode, rem, hg⟩ | ⟨rem, hg⟩ <;> rw [hg] at hg' <;> cases hg'
  · cases h

/-- A group wait that is the last event of its thread starts no base causality step: every step
leads to a later event of its thread, or starts at a write, a fence or an mbarrier arrival. -/
theorem groupWait_last_not_baseStep {X : Execution} {w f : EvId} (hw : GroupWaitEvent X w)
    (hlast : (X.tr w.1).length ≤ w.2 + 1) :
    ¬ (po X w f ∨ CtaBarSync L X w f ∨ MSync L X w f ∨ ClusterSync L X w f ∨
      WarpBarSync L X w f ∨ synchronizesWith L X w f ∨ FenceSync L X w f) := by
  obtain ⟨pc, hg⟩ := hw
  have hne : ∀ {pc' : Nat} {k : Kind}, X.get w = some ⟨pc', k⟩ →
      (∀ mode rem, k ≠ .bulkWait mode rem) → (∀ rem, k ≠ .asyncWait rem) → False := by
    intro pc' k hk h1 h2
    rcases hg with ⟨mode, rem, hg⟩ | ⟨rem, hg⟩ <;> rw [hg] at hk <;> cases hk
    · exact h1 mode rem rfl
    · exact h2 rem rfl
  rintro (⟨h1, h2, h3, -⟩ | ⟨-, key, i, j, ⟨-, ⟨count, pc', mode, hi⟩, -⟩, -, hlt, -⟩ |
    ⟨x, w', m, rs, as, ⟨tx, count, pc', hx⟩, -, -, -, -, -, hx1, hx2⟩ |
    ⟨-, i, j, -, hi, hlt, -⟩ | ⟨i, j, ⟨-, mask, inst, hi, -⟩, hlt, -⟩ |
    ⟨a, b, bs, cs, hwr, -⟩ | h)
  · rw [h1] at hlast
    omega
  · have := len_of_get hi
    simp only at this
    omega
  · have hlen := len_of_get hx
    rcases Nat.lt_or_eq_of_le hx2 with hlt | heq
    · rw [hx1] at hlen
      omega
    · have hxw : x = w := Prod.ext hx1 heq.symm
      subst hxw
      exact hne hx (fun _ _ h => by cases h) (fun _ h => by cases h)
  · omega
  · obtain ⟨pc', hi⟩ := hi
    have := len_of_get hi
    simp only at this
    omega
  · rcases hwr with ⟨pc', hg'⟩ | ⟨old, pc', hg'⟩ <;>
      exact hne hg' (fun _ _ h => by cases h) (fun _ h => by cases h)
  · rcases h with ⟨w', r, a, b, bs, cs, se, sf, hwr, -, -, hh, -⟩ | ⟨⟨s, s', ⟨pc', hg'⟩, -⟩, -⟩
    · rcases hh with ⟨rfl, -⟩ | ⟨sem, ⟨pc', hg'⟩, -⟩
      · rcases hwr with ⟨pc', hg'⟩ | ⟨old, pc', hg'⟩ <;>
          exact hne hg' (fun _ _ h => by cases h) (fun _ h => by cases h)
      · exact hne hg' (fun _ _ h => by cases h) (fun _ h => by cases h)
    · exact hne hg' (fun _ _ h => by cases h) (fun _ h => by cases h)

/-- A group wait that is the last event of its thread precedes nothing in base causality. -/
theorem groupWait_last_not_baseCausality {X : Execution} {w f : EvId} (hw : GroupWaitEvent X w)
    (hlast : (X.tr w.1).length ≤ w.2 + 1) : ¬ baseCausality L X w f := by
  intro h
  obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp h
  exact groupWait_last_not_baseStep hw hlast hb

/-- A group wait that is the last event of its thread precedes no event of its thread. -/
theorem groupWait_last_not_po {X : Execution} {w f : EvId}
    (hlast : (X.tr w.1).length ≤ w.2 + 1) : ¬ po X w f := by
  rintro ⟨h1, h2, h3, -⟩
  rw [h1] at hlast
  omega

/-- Nor does it precede any event through an async proxy fence or a completion observation. -/
theorem groupWait_last_not_completionBefore {X : Execution} {w f : EvId} {l : Loc} {p : Part}
    (hw : GroupWaitEvent X w) (hlast : (X.tr w.1).length ≤ w.2 + 1) :
    ¬ CompletionBefore L X l p w f := by
  cases p
  case mmaRead =>
    rintro ⟨fence, sp, -, -, -, -, -, h, -⟩
    exact groupWait_last_not_baseCausality hw hlast h
  all_goals exact groupWait_last_not_baseCausality hw hlast

/-- A need of a thread instruction that an asynchronous stage fills is the need of that one stage,
and it belongs to a group wait or to a successful poll. -/
theorem needs_async_cases {X : Execution} {j : EvId} {fills : Ref → Prop}
    (hn : Need.node fills ∈ Needs L X j) {i : EvId} {p : Part} (hf : fills (.async i p)) :
    fills = (· = .async i p) ∧
      (GroupWaitEvent X j ∨ ∃ pc m q a s, X.get j = some ⟨pc, .wait m q true a s⟩) := by
  unfold Needs at hn
  cases hg : X.get j with
  | none => simp [hg] at hn
  | some ev =>
    obtain ⟨pc, kd⟩ := ev
    simp only [hg] at hn
    cases kd <;> simp [KindNeeds, maskNeeds, tcNeeds, ctaBarNeeds, ctaBarWarpNeeds,
      clusterNeeds, clusterWarpNeeds, resourceNeeds, groupNeeds, pollNeeds, needsIf,
      warpLanes] at hn
    all_goals try (obtain ⟨a', -, rfl⟩ := hn; obtain ⟨t, h, -⟩ := hf; cases h; done)
    all_goals try (split at hn <;> simp at hn <;> obtain ⟨l, -, rfl⟩ := hn <;>
      (obtain ⟨t, h, -⟩ := hf; cases h))
    case bar =>
      rcases hn with ⟨a', -, rfl⟩ | hn
      · obtain ⟨i, r, -, -, b, h, -⟩ := hf
        cases h
      · rename_i mode
        cases mode
        · simp at hn
          obtain ⟨a1, b1, -, -, rfl⟩ := hn
          cases hf
        · simp at hn
    case cluster =>
      rcases hn with ⟨a', -, rfl⟩ | hn
      · obtain ⟨i, r, -, -, b, h, -⟩ := hf
        cases h
      · rename_i op
        cases op
        · simp at hn
        · simp at hn
          obtain ⟨a1, b1, -, -, rfl⟩ := hn
          cases hf
    case wait =>
      obtain ⟨hok, r, -, -, rfl⟩ := hn
      subst hok
      refine ⟨by rw [hf], .inr ⟨_, _, _, _, _, rfl⟩⟩
    case bulkWait =>
      obtain ⟨a', -, -, q, -, rfl⟩ := hn
      refine ⟨by rw [hf], .inl ⟨pc, .inl ⟨_, _, hg⟩⟩⟩
    case asyncWait =>
      obtain ⟨a', -, -, q, -, rfl⟩ := hn
      refine ⟨by rw [hf], .inl ⟨pc, .inr ⟨_, hg⟩⟩⟩
    case tc =>
      rename_i k
      cases k <;> simp at hn
      all_goals try (obtain ⟨a', -, rfl⟩ := hn; obtain ⟨t, h, -⟩ := hf; cases h; done)
      rename_i group dst request
      rcases hn with ⟨a, -, rfl⟩ | ⟨-, hn | hn⟩ | hresult
      · obtain ⟨t, h, -⟩ := hf
        cases h
      · cases group <;> simp at hn
        obtain ⟨l, rfl⟩ := hn
        obtain ⟨a, b, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := hf <;> cases h
      · cases request <;> simp at hn
        obtain ⟨a1, -, -, l, rfl⟩ := hn
        obtain ⟨d, -, h⟩ := hf
        cases h
      · cases Tmem.Pair.allocResultNeeds_node L hresult
        exact hf.elim

/-- A wait that a stage absent from `X` witnesses in an extension with the same needs is a group
wait that has not returned in `X`: a returned wait is ready (DEP-ORDER), and a successful poll has
returned. -/
theorem witness_absent_pending {X Y : Execution} {w i : EvId} {p : Part}
    (hready : ∀ e, Returned X e → Ready L X e) (hneeds : Needs L Y w = Needs L X w)
    (hx : ¬ X.RefPresent (.async i p)) (h : Witness L Y (.async i p) w) :
    GroupWaitEvent X w ∧ ¬ Returned X w := by
  obtain ⟨fills, hn, -, hf⟩ := h
  rw [hneeds] at hn
  obtain ⟨rfl, hk⟩ := needs_async_cases hn hf
  have hr := not_returned_of_need (hready w) hn hx
  refine ⟨?_, hr⟩
  rcases hk with hk | ⟨pc, m, q, a, s, hg⟩
  · exact hk
  · exact (hr (by unfold Returned; simp [hg])).elim

/-- The new stages `N` of an extension `Y` together with the returns of the waits that a new stage
witnesses. -/
def CompletionNodes (L : Launch) (Y : Execution) (N : Ref → Prop) (n : Ref × Bool) : Prop :=
  N n.1 ∨ (n.2 = true ∧ ∃ w x, n.1 = .thread w ∧ N x ∧ Witness L Y x w)

/-- **Appending completion stages is a sink frame.** The new stages `N` lead by `Waits` only to
their own completion points and to the returns of the waits they witness, and those returns lead
nowhere (`hpend`, from `groupWait_return_not_waits`). Outside these nodes the order relations of
`Y` are those of `X`, which the remaining hypotheses state relation by relation. -/
theorem sinkFrame_completion {K : Kernel} {A : List Assumption} {X Y : Execution}
    (N : Ref → Prop) (hthr : ∀ j, ¬ N (.thread j))
    (hnew : ∀ u v, N u.1 → Waits L Y u v → (N v.1 ∧ u.2 = false ∧ v.2 = true) ∨
      (u.2 = false ∧ v.2 = true ∧ ∃ w, v.1 = .thread w ∧ Witness L Y u.1 w))
    (hpend : ∀ w x, N x → Witness L Y x w → ∀ v, ¬ Waits L Y (.thread w, true) v)
    (hstage : ∀ u v, ¬ CompletionNodes L Y N u → ¬ CompletionNodes L Y N v →
      stageCausality L Y u v → Relation.TransGen (stageCausality L X) u v)
    (hsync : ∀ x w, ¬ CompletionNodes L Y N (x, false) → ¬ CompletionNodes L Y N (w, true) →
      SyncObserved L Y x w → SyncObserved L X x w)
    (hobject : ∀ o u v, ¬ CompletionNodes L Y N u → ¬ CompletionNodes L Y N v →
      ObjectOrder L Y o u v → ObjectOrder L X o u v)
    (hobjectSync : ∀ o u v, ¬ CompletionNodes L Y N u → ¬ CompletionNodes L Y N v →
      SyncObjectOrder L Y o u v → SyncObjectOrder L X o u v)
    (hdep : ∀ u v, ¬ CompletionNodes L Y N u → ¬ CompletionNodes L Y N v →
      DepStep L K Y u v → Relation.TransGen (DepStep L K X) u v)
    (hasyncSelf : ∀ m i p y, MBarrier.Before (Y.objects m) (.async i p) y →
      ¬ ∃ j, y = .thread j ∧ j.1 = i.1 ∧ j.2 < i.2)
    (hasyncObserved : ∀ m i p y, ¬ CompletionNodes L Y N (.async i p, true) →
      ¬ CompletionNodes L Y N (y, true) →
      (MbarLifetimeRecord Y m y ∨
          ∃ j ws, y = .thread j ∧ AsyncCopy.WaitObserves Y (.async i p) j m true ws) →
        (MbarLifetimeRecord X m y ∨
          ∃ j ws, y = .thread j ∧ AsyncCopy.WaitObserves X (.async i p) j m true ws))
    (hinit : InitFenceOrdered L X)
    (hinitSync : ∀ m init w, InitFenceSync L Y m init w → InitFenceSync L X m init w)
    (hinitBefore : ∀ m y init, MBarrier.Before (Y.objects m) y (.thread init) →
      MBarrier.Before (X.objects m) y (.thread init))
    (hget : ∀ e, Y.get e = X.get e) :
    SinkFrame L K A X Y (CompletionNodes L Y N) := by
  classical
  have hrank : ∀ u v, Waits L Y u v → CompletionNodes L Y N u →
      CompletionNodes L Y N v ∧
        (fun n : Ref × Bool => if N n.1 then (if n.2 then 1 else 0) else 2) u <
        (fun n : Ref × Bool => if N n.1 then (if n.2 then 1 else 0) else 2) v := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ h (hu | ⟨hb, w, x, he, hx, hw⟩)
    · rcases hnew _ _ hu h with ⟨hv, hb, hb'⟩ | ⟨hb, hb', w, hf, hw⟩
      · simp only at hu hv hb hb'
        subst hb hb'
        exact ⟨.inl hv, by simp [hu, hv]⟩
      · simp only at hu hf hb hb' hw
        subst hb hb' hf
        refine ⟨.inr ⟨rfl, w, e, rfl, hu, hw⟩, ?_⟩
        simp [hu, hthr]
    · simp only at hb he
      subst hb he
      exact (hpend w x hx hw _ h).elim
  refine ⟨⟨_, hrank⟩, hstage, hsync, hobject, hobjectSync, hdep, ?_, hasyncSelf,
    hasyncObserved, ?_, fun e _ => hget e⟩
  · rintro m i p y - (hi | ⟨hb, -⟩)
    · exact (hthr i hi).elim
    · cases hb
  · intro m init w y hs ht hb
    have hy : ¬ CompletionNodes L Y N (.thread y.issuer, false) := by
      rintro (hy | ⟨hb, -⟩)
      · exact hthr _ hy
      · cases hb
    exact hinit m init w y (hinitSync m init w hs)
      (SinkFrame.old_path hrank (fun _ _ h => stageCausality.waits h) hstage ht hy).2
      (hinitBefore m y init hb)

/-- A group wait of `Y` that waits for a stage absent from `X` has not returned in `X`. -/
theorem groupWait_absent_pending {X Y : Execution} {k : GroupWait} {j w : EvId} {q : Part}
    (hready : ∀ e, Returned X e → Ready L X e) (hneeds : Needs L Y w = Needs L X w)
    (hw : GroupWaitsFor Y k j w) (hq : q ∈ GroupWaitStages Y j k) (hy : Y.AsyncPresent j q)
    (hx : ¬ X.AsyncPresent j q) : GroupWaitEvent X w ∧ ¬ Returned X w :=
  witness_absent_pending hready hneeds hx (GroupWaitsFor.witness hw hq hy)

/-- In an extension that adds stages, an observed completion is one of `X` or is observed by a
group wait that has not returned in `X`. -/
theorem asyncFinished_completion {X Y : Execution} (hready : ∀ e, Returned X e → Ready L X e)
    (hneeds : ∀ e, Needs L Y e = Needs L X e)
    (hgw : ∀ k j w, GroupWaitsFor Y k j w → GroupWaitsFor X k j w)
    (hst : ∀ j k, GroupWaitStages Y j k = GroupWaitStages X j k)
    (hobs : ∀ j p w ws, AsyncObserved Y j p w true ws → AsyncObserved X j p w true ws)
    {j : EvId} {p : Part} {w : EvId} (h : AsyncFinished L Y j p w) :
    AsyncFinished L X j p w ∨ (GroupWaitEvent X w ∧ ¬ Returned X w) := by
  classical
  rcases h with ⟨k, hv, hw, hall⟩ | ⟨ws, ho, hsc⟩
  · by_cases hx : ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q
    · exact .inl (.inl ⟨k, hv, hgw k j w hw, hx⟩)
    · push Not at hx
      obtain ⟨q, hq, hxq⟩ := hx
      rw [← hst] at hq
      exact .inr (groupWait_absent_pending hready (hneeds w) hw hq (hall q hq) hxq)
  · exact .inl (.inr ⟨ws, hobs j p w ws ho, hsc⟩)

/-- The same for a completion observed only in the async proxy. -/
theorem asyncOnlyFinished_completion {X Y : Execution}
    (hready : ∀ e, Returned X e → Ready L X e) (hneeds : ∀ e, Needs L Y e = Needs L X e)
    (hgw : ∀ k j w, GroupWaitsFor Y k j w → GroupWaitsFor X k j w)
    (hst : ∀ j k, GroupWaitStages Y j k = GroupWaitStages X j k)
    {j : EvId} {p : Part} {w : EvId} (h : AsyncOnlyFinished Y j p w) :
    AsyncOnlyFinished X j p w ∨ (GroupWaitEvent X w ∧ ¬ Returned X w) := by
  classical
  obtain ⟨hv, hw, hall⟩ := h
  by_cases hx : ∀ q ∈ GroupWaitStages X j (.bulk .asyncProxy), X.AsyncPresent j q
  · exact .inl ⟨hv, hgw _ j w hw, hx⟩
  · push Not at hx
    obtain ⟨q, hq, hxq⟩ := hx
    rw [← hst] at hq
    exact .inr (groupWait_absent_pending hready (hneeds w) hw hq (hall q hq) hxq)

section transfer
variable {X Y : Execution}
  (htm : ∀ a b, AsyncCopy.TracksMma Y a b → AsyncCopy.TracksMma X a b)
  (htc : ∀ a b, AsyncCopy.TracksCpAsync Y a b → AsyncCopy.TracksCpAsync X a b)

include htm htc in
/-- A stage edge of `Y` between two stages present in `X` is one of `X`, when the tracked
operations of a commit and of a `cp.async.mbarrier.arrive` are those of `X`. -/
theorem StageEdge.transfer {e f : Ref} (he : Y.RefPresent e → X.RefPresent e)
    (hf : Y.RefPresent f → X.RefPresent f) (h : StageEdge Y e f) : StageEdge X e f := by
  unfold StageEdge at h ⊢
  split at h
  all_goals first
    | exact h.elim
    | exact ⟨h.1, he h.2.1, hf h.2.2⟩
    | exact ⟨h.1, h.2.1, he h.2.2.1, hf h.2.2.2⟩
    | exact ⟨htm _ _ h.1, he h.2.1, hf h.2.2⟩
    | exact ⟨htc _ _ h.1, he h.2.1, hf h.2.2⟩

include htm htc in
/-- The stage order of `Y` between nodes whose presence is that of `X` is that of `X`. -/
theorem StageOrder.transfer {e f : Ref} {b b' : Bool} (he : Y.RefPresent e → X.RefPresent e)
    (hf : Y.RefPresent f → X.RefPresent f) (h : StageOrder Y (e, b) (f, b')) :
    StageOrder X (e, b) (f, b') :=
  h.imp (fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, he h4⟩)
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, StageEdge.transfer htm htc he hf h3⟩

end transfer

/-- The issue of a stage of `Y` whose presence is that of `X` is an issue of `X`. -/
theorem IssueStage.transfer {X Y : Execution} {e f : Ref} {b b' : Bool}
    (hget : ∀ e, Y.get e = X.get e) (hf : Y.RefPresent f → X.RefPresent f)
    (h : IssueStage Y (e, b) (f, b')) : IssueStage X (e, b) (f, b') := by
  obtain ⟨h1, h2, j, p, he, hfe, hr, hp, hm⟩ := h
  subst he hfe
  obtain ⟨ev, hev⟩ := hr
  exact ⟨h1, h2, j, p, rfl, rfl, ⟨ev, (hget j).symm.trans hev⟩, hf hp, hm⟩

/-- A fresh record appended to an object history is observed by no wait: a wait observes only the
updates recorded before it. -/
theorem appendObject_not_observed {X : Execution} {m : Loc} {r : MBarrier.Record Ref}
    (hfresh : ∀ l q, q ∈ X.objects l → q.id ≠ r.id) (hth : ∀ e, r.id ≠ .thread e) (w : Ref) :
    ¬ MbarObserved (X.appendObject m r) r.id w := by
  rintro ⟨-, j, l, acq, ws, rfl, ⟨-, hu⟩, -⟩
  rw [appendObject_update_iff (hth j)] at hu
  obtain ⟨a, b, q, x, phase, hq, hid, -⟩ := hu
  exact hfresh l q (List.mem_of_getElem? hq) hid

/-- Appending a fresh record of an asynchronous update to an object history changes no need. -/
theorem appendObject_needs {X : Execution} {m : Loc} {r : MBarrier.Record Ref}
    (hfresh : ∀ l q, q ∈ X.objects l → q.id ≠ r.id) (hth : ∀ e, r.id ≠ .thread e) (e : EvId) :
    Needs L (X.appendObject m r) e = Needs L X e := by
  refine needs_congr (X := X) (Y := X.appendObject m r) (fun _ => rfl)
    (fun k _ hk => by
      cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl))
    (fun e l => ?_) e
  have hobs : ∀ q ∈ X.objects l, needsIf (MbarObserved (X.appendObject m r) q.id (.thread e))
      [Need.node (· = q.id)] =
        needsIf (MbarObserved X q.id (.thread e)) [Need.node (· = q.id)] := by
    intro q hq
    unfold needsIf
    rw [propext (appendObject_mbarObserved_iff (Ne.symm (hfresh l q hq)) (hth e))]
  have hnone : needsIf (MbarObserved (X.appendObject m r) r.id (.thread e))
      [Need.node (· = r.id)] = [] := by
    unfold needsIf
    split
    · exact absurd ‹_› (appendObject_not_observed hfresh hth _)
    · rfl
  unfold pollNeeds
  by_cases hl : l = m
  · subst hl
    rw [show (X.appendObject l r).objects l = X.objects l ++ [r] by simp [Execution.appendObject],
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, hnone,
      List.append_nil]
    exact List.flatMap_congr hobs
  · rw [show (X.appendObject m r).objects l = X.objects l by simp [Execution.appendObject, hl]]
    exact List.flatMap_congr hobs

/-- A node that fills no need of `X` witnesses no wait of an extension with the same needs. -/
theorem not_witness_of_needRef {X Y : Execution} {x : Ref} {w : EvId}
    (hneeds : Needs L Y w = Needs L X w) (hx : ¬ NeedRef X x) : ¬ Witness L Y x w := by
  rintro ⟨fills, hn, -, hf⟩
  rw [hneeds] at hn
  exact hx (needs_node_cases hn hf)

end
end PTX
