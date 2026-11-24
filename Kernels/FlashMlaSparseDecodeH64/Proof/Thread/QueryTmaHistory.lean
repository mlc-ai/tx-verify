-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GemmReuseEndpoints
public import Lemmas.Flow.TraceInduction
import Lemmas.Flow.Final

@[expose] public section

/-! # The query TMA issues and their successful wait precede the Tensor Memory copies -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTmaHistory

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

private def stage : Wg1Mma.Site → Nat
  | .qLoad k => k.val
  | .qArrive => 8
  | .qWait => 9
  | .qFence | .qCopy _ | .qCopyCommit | .qCopyWait | .qCopyFence
  | .kvWait | .kvFence | .qkMma _ | .qkCommit | .soWait | .soFence | .pvMma _ | .pvCommit => 10
  | _ => 0

private def captured (k : Nat) (d : Wg1Mma.D) (e : Event) : Prop :=
  (∃ tile : Fin 8, tile.val = k ∧ d.site = .qLoad tile) ∨
    (k = 8 ∧ d.site = .qArrive) ∨
    (k = 9 ∧ d.site = .qWait ∧ ∃ m p acq sc, e.kind = .wait m p true acq sc)

set_option maxHeartbeats 1200000 in
private theorem advance {k : Nat} {d d' : Wg1Mma.D} {e : Event}
    (hn : Wg1Mma.next P L g d e = some (some d')) (hk : k < stage d'.site) :
    k < stage d.site ∨ captured k d e := by
  cases hd : d.site <;> simp only [Wg1Mma.next, hd, Wg1Mma.nextSite] at hn
  case qLoad old =>
    have hl := old.isLt
    split at hn <;> cases hn <;> simp only [stage] at hk ⊢
    all_goals
      by_cases h : old.val = k
      · exact .inr (.inl ⟨old, h, hd⟩)
      · exact .inl (by omega)
  case qArrive =>
    cases hn
    have hNext : k < 9 := hk
    by_cases h : k = 8
    · exact .inr (.inr (.inl ⟨h, hd⟩))
    · exact .inl (show k < 8 by omega)
  case qWait =>
    cases he : e.kind <;> simp [he] at hn
    rename_i m p ok acq sc
    cases ok <;> simp at hn <;> cases hn
    · exact .inl (by simpa [hd] using hk)
    · have hp : k < 10 := hk
      by_cases h : k = 9
      · exact .inr (.inr (.inr ⟨h, hd, m, p, acq, sc, he⟩))
      · exact .inl (show k < 9 by omega)
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    try simp only [Wg1Mma.startSite, Wg1Mma.afterTopk] at hk
    repeat' split_ifs at hk
    all_goals simp_all [stage]

private def needs (k : Nat) : Option Machine.ThreadD → Prop
  | some (.mma d) => k < stage d.site
  | _ => False

private def source (P : Params) (L : Launch) (g k : Nat) (pre : List Event) : Prop :=
  ∃ j d e o, pre[j]? = some e ∧
    (Machine.machine P L g).after (some (.prologue .shfl0)) (pre.take j) =
      some (some (.mma d)) ∧
    captured k d e ∧ (Machine.machine P L g).Fired (some (.mma d)) e o

private def history (P : Params) (L : Launch) (g k : Nat)
    (s : Option Machine.ThreadD) (pre : List Event) : Prop :=
  (Machine.machine P L g).after (some (.prologue .shfl0)) pre = some s ∧
    (needs k s → source P L g k pre)

private theorem source_append {k : Nat} {pre : List Event} {e : Event}
    (h : source P L g k pre) : source P L g k (pre ++ [e]) := by
  obtain ⟨j, d, f, o, hf, ha, hcap, hfire⟩ := h
  have hj := (List.getElem?_eq_some_iff.mp hf).1
  refine ⟨j, d, f, o, ?_, ?_, hcap, hfire⟩
  · rwa [List.getElem?_append_left hj]
  · rwa [List.take_append_of_le_length hj.le]

private theorem history_step {k : Nat} {s s' : Option Machine.ThreadD}
    {pre : List Event} {e : Event} {o : Option TState}
    (h : history P L g k s pre) (hf : (Machine.machine P L g).Fired s e o)
    (hn : (Machine.machine P L g).next s e = some s') :
    history P L g k s' (pre ++ [e]) := by
  refine ⟨?_, ?_⟩
  · rw [Machine.after_snoc (M := Machine.machine P L g) (some (.prologue .shfl0)) pre e, h.1]
    exact hn
  intro hw
  cases s with
  | none =>
    change some none = some s' at hn
    cases hn
    exact hw.elim
  | some s =>
    change Machine.next P L g s e = some s' at hn
    cases s
    case mma d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hnext
        cases hn
        rcases advance hnext hw with hprev | hcap
        · exact source_append (h.2 hprev)
        · refine ⟨pre.length, d, e, o, by simp, ?_, hcap, hf⟩
          rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
          exact h.1
      · split_ifs at hn <;> cases hn <;> exact hw.elim
      · split_ifs at hn
        cases hn
        exact hw.elim
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        exact hw.elim
      · split at hn
        · rename_i w _
          split_ifs at hn <;> fin_cases w <;> cases hn <;> exact hw.elim
        · cases hn
          exact hw.elim
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> first
        | exact hw.elim
        | exact ((Nat.not_lt_zero k) hw).elim
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals exact hw.elim

variable {mem0 : Mem0} {X : Execution}

private theorem source_before_live {k i : Nat} {d : Wg1Mma.D}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hg : g < L.threads)
    (hlive : ∀ j < i, ∀ f, X.get (g, j) = some f → ¬ Ends f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hk : k < stage d.site) :
    ∃ j < i, ∃ q f u, X.get (g, j) = some f ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma q)) ∧ captured k q f ∧
      (Machine.machine P L g).Fired (some (.mma q)) f (some u) := by
  have hr := (hs.produces (hX.thr g hg)).prefix_induction (history P L g k)
    ⟨rfl, False.elim⟩ (fun _ _ _ _ _ => history_step) i (some (.mma d)) hd
  obtain ⟨j, q, f, o, hf, hstate, hcap, hfire⟩ := hr.2 hk
  have hj := (List.getElem?_eq_some_iff.mp hf).1
  have hji : j < i := hj.trans_le (List.length_take_le _ _)
  have hget : X.get (g, j) = some f := List.getElem?_eq_some_iff.mpr
    ⟨hj.trans_le (List.length_take_le' _ _), by simpa using (List.getElem?_eq_some_iff.mp hf).2⟩
  rw [List.take_take, Nat.min_eq_left hji.le] at hstate
  cases o with
  | none =>
    obtain ⟨t, _, hf⟩ := hfire
    exact (hlive j hji f hget (fires_none_ends hf)).elim
  | some u => exact ⟨j, hji, q, f, u, hget, hstate, hcap, hfire⟩

private theorem no_end_before_event {i : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get (g, i) = some e) :
    ∀ j < i, ∀ f, X.get (g, j) = some f → ¬ Ends f := by
  intro j hj f hf hEnd
  obtain ⟨_, hrun⟩ := hX.thr g (Frame.lt_of_get hX he)
  have hLast := PTX.Flow.Run.end_last hrun hf hEnd
  have hi := PTX.len_of_get he
  change i < (X.tr g).length at hi
  omega

private theorem source_before {k i : Nat} {d : Wg1Mma.D} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hk : k < stage d.site) :
    ∃ j < i, ∃ q f u, X.get (g, j) = some f ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma q)) ∧ captured k q f ∧
      (Machine.machine P L g).Fired (some (.mma q)) f (some u) :=
  source_before_live hX hs (Frame.lt_of_get hX he) (no_end_before_event hX he) hd hk

private theorem wait_before_marked {i : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : 9 < stage d.site) :
    ∃ j < i, ∃ q tag,
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma q)) ∧ q.site = .qWait ∧
      X.get (g, j) = some
        ⟨tag, .wait ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ 0 true true .cta⟩ := by
  obtain ⟨j, hj, q, f, u, hget, hstate, hcap, hf⟩ :=
    source_before (k := 9) hX hs he hd hsite
  rcases hcap with ⟨tile, hval, _⟩ | ⟨h, _⟩ | ⟨_, hq, _, _, _, _, hok⟩
  · have := tile.isLt
    omega
  · omega
  · obtain ⟨ok, hk⟩ := RingEvents.mma_wait_exact hpre (.inl hq) hf
    have hk' : f.kind = .wait ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩
        0 ok true .cta := by simpa [hq, ctaOf] using hk
    have hv := (Kind.wait.inj (hk'.symm.trans hok)).2.2.1
    obtain ⟨tag, kind⟩ := f
    change kind = _ at hk'
    rw [hv] at hk'
    exact ⟨j, hj, q, tag, hstate, hq, by rw [hget, hk']⟩

/-- Every actual query copy has a preceding successful query TMA wait in its own thread. -/
theorem wait_before_copy {i : Nat} {d : Wg1Mma.D} {k : Fin 16} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qCopy k) :
    ∃ j < i, ∃ q tag,
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma q)) ∧ q.site = .qWait ∧
      X.get (g, j) = some
        ⟨tag, .wait ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ 0 true true .cta⟩ :=
  wait_before_marked hpre hX hs he hd (by simp [hsite, stage])

/-- Every actual MMA loop event follows the lane's successful query TMA wait. -/
theorem wait_before_loop {i : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : Wg1Mma.LoopSite d.site) :
    ∃ j < i, ∃ q tag,
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma q)) ∧ q.site = .qWait ∧
      X.get (g, j) = some
        ⟨tag, .wait ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ 0 true true .cta⟩ := by
  apply wait_before_marked hpre hX hs he hd
  cases h : d.site <;> simp_all [Wg1Mma.LoopSite, stage]

private theorem load_before_wait_live {i : Nat} {d : Wg1Mma.D} (tile : Fin 8)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads)
    (hlive : ∀ j < i, ∀ f, X.get (g, j) = some f → ¬ Ends f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qWait) :
    ∃ j < i, X.TensorIssue (g, j) (P.param1Base + Wg1Mma.qMapOff)
      (MmaDataTrace.queryTmaSpec P L g tile) := by
  obtain ⟨j, hj, q, f, u, hget, _, hcap, hf⟩ :=
    source_before_live (k := tile.val) hX hs hg hlive hd (by
      rw [hsite]
      have := tile.isLt
      change tile.val < 9
      omega)
  rcases hcap with ⟨t, ht, hql⟩ | ⟨ht, _⟩ | ⟨ht, _, _⟩
  · have heq : t = tile := Fin.ext ht
    subst t
    obtain ⟨t, ⟨hat, _⟩, hfire⟩ := hf
    change (Wg1Mma.code P L g).AtD q t at hat
    change Fires t.pc (match kernel.code[q.site.pc]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) f (some u) at hfire
    have hpc : t.pc = q.site.pc := hat.1
    rw [hpc, hql] at hfire
    have hq : q = ⟨.qLoad tile, q.i⟩ := by cases q; simp_all
    rw [hq] at hat
    cases hc : kernel.code[(Wg1Mma.Site.qLoad tile).pc]? with
    | none =>
      rw [hc] at hfire
      cases hfire.2
    | some ins =>
      rw [hc] at hfire
      have hw := (MmaDataTrace.fires_qLoad hpre hg q.i tile hat hc hfire).1
      obtain ⟨tag, kind⟩ := f
      exact ⟨j, hj, tag, by rw [hget, ← hw]⟩
  · have := tile.isLt
    omega
  · have := tile.isLt
    omega

/-- Each selected query tile has its actual TMA issue before the query wait. -/
theorem load_before_wait {i : Nat} {d : Wg1Mma.D} {e : Event} (tile : Fin 8)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qWait) :
    ∃ j < i, X.TensorIssue (g, j) (P.param1Base + Wg1Mma.qMapOff)
      (MmaDataTrace.queryTmaSpec P L g tile) :=
  load_before_wait_live tile hpre hX hs (Frame.lt_of_get hX he)
    (no_end_before_event hX he) hd hsite

private theorem no_end_in_pending (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) :
    ∀ j < (X.tr g).length, ∀ f, X.get (g, j) = some f → ¬ Ends f := by
  intro j hj f hf hEnd
  obtain ⟨tag, kind⟩ := f
  rcases hEnd with ⟨fault, hKind⟩ | hKind
  · change kind = .ub fault at hKind
    subst kind
    exact hub ⟨(g, j), tag, fault, hf⟩
  · change kind = .exit at hKind
    subst kind
    obtain ⟨_, hrun⟩ := hX.thr g hp.1
    have hLast := PTX.Flow.Run.end_last hrun hf (.inr rfl)
    apply hp.2.2 tag
    rw [List.getLast?_eq_getElem?, ← hLast]
    simpa only [Nat.add_sub_cancel, Execution.get] using hf

/-- A pending query TMA wait has already issued its eight real tile loads. -/
theorem load_before_pending_wait {d : Wg1Mma.D} (tile : Fin 8)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hub : ¬ HasUb X) (hp : Frame.Pending L X g)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hsite : d.site = .qWait) :
    ∃ j < (X.tr g).length, X.TensorIssue (g, j) (P.param1Base + Wg1Mma.qMapOff)
      (MmaDataTrace.queryTmaSpec P L g tile) := by
  exact load_before_wait_live tile hpre hX hs hp.1 (no_end_in_pending hX hub hp) hd hsite

/-- A pending query TMA poll follows its elected lane's actual expect-tx. -/
theorem arrival_before_pending_wait {d : Wg1Mma.D} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hsite : d.site = .qWait) :
    ∃ j < (X.tr g).length, ∃ tag,
      X.get (g, j) = some
        ⟨tag, .arrive ⟨.shared, ctaOf L g, L.sharedBase + 222776⟩ 65536 1 true .cta⟩ := by
  obtain ⟨j, hj, q, f, u, hget, _, hcap, hf⟩ := source_before_live (k := 8)
    hX hs hp.1 (no_end_in_pending hX hub hp) hd (by rw [hsite]; decide)
  rcases hcap with ⟨k, h, _⟩ | ⟨_, hq⟩ | ⟨h, _, _⟩
  · have := k.isLt
    omega
  · have hk := RingEvents.query_expectTx hpre hq hf
    obtain ⟨tag, kind⟩ := f
    change kind = _ at hk
    exact ⟨j, hj, tag, by rw [hget, hk]; rfl⟩
  · omega


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTmaHistory
