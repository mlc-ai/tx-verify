-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.ExtensionSnoc
public import Lemmas.Snoc.ObjectEventExtend
public import Lemmas.Tmem.TmemPairExtend
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.MBarrier.MBarrierPhase
public import Lemmas.Step.PollPreserve
public import Lemmas.Execution.ExecutionCountedPrefixSize

@[expose] public section

/-! # A thread whose last event no longer blocks

A proof tool. A thread's last event that blocks (`Kind.resume = .blocking false`: a CTA or
cluster barrier, a register request, a group wait, a Tensor Memory allocation-management event,
a warp-collective `tcgen05` event) must be ready (`Ready`, DEP-ORDER) before the thread performs
its next event, since that next event makes it returned. `Released` says it is ready
(`LastReady`), so the thread may perform its next event. An acquire poll of a released thread,
successful or failed, keeps the execution consistent (`poll_consistent`); a ready one is a counted
extension (`poll_counted_extension`). The progress argument splits a pending thread into a
blocking last event that is not ready and a released one (the thread's next event). -/

namespace PTX.Step
open PTX AsyncCopy MBarrier
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution} {mem0 : Mem0}

/-- The thread's last event, if it blocks, is ready. -/
structure Released (L : Launch) (X : Execution) (g : Nat) : Prop where
  ready : LastReady L X g

/-- A last event that does not block, or none at all, needs no release. -/
theorem Released.of_get {g : Nat}
    (h : ∀ q, X.get (g, (X.tr g).length - 1) = some q → q.kind.resume ≠ .blocking false) :
    Released L X g :=
  ⟨fun _ _ hq hk => (h _ hq hk).elim⟩

/-- A poll is ready: each record it observed is present (`MbarObserved`). -/
theorem ready_of_wait {e : EvId} {pc : Nat} {m : Loc} {p : Nat} {ok acq : Bool}
    {sc : MbarScope} (he : X.get e = some ⟨pc, .wait m p ok acq sc⟩) : Ready L X e := by
  intro n hn
  simp only [Needs, he] at hn
  cases ok
  · simp [KindNeeds] at hn
  simp only [KindNeeds, ite_true, pollNeeds] at hn
  obtain ⟨r, -, hm⟩ := List.mem_flatMap.mp hn
  by_cases hob : MbarObserved X r.id (.thread e)
  · simp only [needsIf, hob, ite_true, List.mem_singleton] at hm
    subst hm
    exact ⟨r.id, hob.1, rfl⟩
  · simp [needsIf, hob] at hm

/-- An appended wait keeps the Fence-SC obligation when causality into an old event is causality
of `X` (MEM-FENCE-SC): its object record changes no `fence.sc` event and no morally strong pair. -/
theorem snocObject_fenceScOk {g : Nat} {e : Event} {r : Nat → Option Ref} {mb : Loc}
    {rec : Record Ref} (h : FenceScOk L X (baseCausality L X))
    (hsc : ∀ s, e.kind ≠ .fence .sc s)
    (hold : ∀ a b, b.2 < (X.tr b.1).length → baseCausality L (X.snocObject g e r mb rec) a b →
      baseCausality L X a b) :
    FenceScOk L (X.snocObject g e r mb rec) (baseCausality L (X.snocObject g e r mb rec)) := by
  have hfence : ∀ {v s}, (X.snocObject g e r mb rec).ThreadFence v .sc s →
      v.2 < (X.tr v.1).length ∧ X.ThreadFence v .sc s := by
    rintro v s ⟨pc, hv⟩
    change (X.snoc g e r).get v = _ at hv
    rw [snoc_get] at hv
    split_ifs at hv
    · exact (hsc s (by rw [Option.some.inj hv])).elim
    · exact ⟨len_of_get hv, pc, hv⟩
  have hstrong : ∀ {a b}, ScStrong L (X.snocObject g e r mb rec) a b →
      b.2 < (X.tr b.1).length ∧ ScStrong L X a b := by
    rintro a b ⟨s, s', ha, hb, hscope⟩
    exact ⟨(hfence hb).1, s, s', (hfence ha).2, (hfence hb).2, hscope⟩
  refine ⟨fun a b hs hne => h.total a b (hstrong hs).2 hne, fun a ha => h.acyclic a ?_,
    fun a b hs hc => h.causal a b (hstrong hs).2 (hold a b (hstrong hs).1 hc)⟩
  exact Relation.TransGen.mono (fun x y hxy => ⟨(hstrong hxy.1).2, hxy.2⟩) _ _ ha

/-- **A released thread performs an acquire poll** of `m`, recorded in the history of `m` by
`rec`, a checked poll record of the thread's next index: the execution stays consistent.
Successful and failed polls differ only in the record. -/
theorem poll_consistent (hX : Consistent L K A mem0 X) {g pc parity : Nat} {ok : Bool}
    {m : Loc} {scope : MbarScope} (hg : g < L.threads) (hne : X.tr g ≠ [])
    (hrel : Released L X g)
    (hasm : ∀ a ∈ A, ∀ {rec : Record Ref}, rec.id = .thread (g, (X.tr g).length) →
      a.wf L mem0 (X.snocObject g ⟨pc, .wait m parity ok true scope⟩ (fun _ => none) m rec))
    {t t1 u : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 ⟨pc, .wait m parity ok true scope⟩ (some u)) {rec : Record Ref}
    (hid : rec.id = .thread (g, (X.tr g).length)) (hact : rec.action = .pollParity parity ok)
    (hreply : rec.reply.waited = some ok)
    (hok : RecordOk (stateBefore (X.objects m) (X.objects m).length) rec) :
    Consistent L K A mem0
      (X.snocObject g ⟨pc, .wait m parity ok true scope⟩ (fun _ => none) m rec) := by
  let ev : Event := ⟨pc, .wait m parity ok true scope⟩
  have hshape : ev.kind = .wait m parity ok true scope := rfl
  have htc : ∀ k, ev.kind ≠ .tc k := by intros; simp [ev]
  have hnb : ∀ id count mode, ev.kind ≠ .bar id count mode := by intros; simp [ev]
  have hns : ∀ mode a b c recv ok, ev.kind ≠ .shfl mode a b c recv ok := by
    intros; simp [ev]
  have hrd : ∀ a bs, ev.kind ≠ .rd a bs := by intros; simp [ev]
  have hwr : ∀ a bs, ev.kind ≠ .wr a bs := by intros; simp [ev]
  have hrmw : ∀ a old new, ev.kind ≠ .rmw a old new := by intros; simp [ev]
  have hna : ∀ m tx count sc, ev.kind ≠ .arrive m tx count true sc := by intros; simp [ev]
  have hchecked : CheckedLog (X.objects m ++ [rec]) := by
    have hh := (hX.tma.2.2.1 m).1.prefix (Nat.le_refl (X.objects m).length)
    rw [List.take_length] at hh
    apply CheckedLog.snoc hh (hX.tma.2.2.1 m).1.1 ?_ hok
    intro hm
    obtain ⟨q, hq, hqid⟩ := List.mem_map.mp hm
    exact snoc_fresh_object_id hX.tma hq (hqid.trans hid)
  have hobjects : ObjectsOk (X.snocObject g ev (fun _ => none) m rec) := by
    apply snoc_objects_checked hX.effectValidity htc m rec hid ?_ hchecked ?_
    · intro l
      simp only [objectAction, snoc_get_new, hact]
      by_cases hm : l = m
      · simp [ev, hm]
      · simp [ev, hm, Ne.symm hm]
    · intro p ok' hh _
      rw [hact, Action.pollParity.injEq] at hh
      rw [hreply, hh.2]
  apply consistent_snoc_history hX hg hrun hl he htc hns hrd hwr hrmw (by intro h; cases h)
    hrel.ready (records := fun l => if l = m then X.objects m ++ [rec] else X.objects l)
    (SnocRecords.append hid)
    (fun _ => ready_of_wait (by
      change (X.snoc g ev (fun _ => none)).get (X.newId g) = _
      exact snoc_get_new))
  · exact PTX.snocObject_tma hX.effectValidity htc hobjects
  · exact poll_object_orderOk hX htc hshape hns m rec hid
  · exact snocObject_noFuture hX hshape hid htc hrd hnb hna
  · exact snocObject_hidden hX hshape hid htc hrd hwr hnb hna
  · intro a ha
    exact hasm a ha hid
  · exact ExtensionObligations.snocObject_plain hX trivial (.inl hne) (by intro h; cases h)
      hrmw rfl (by intro s h; cases h)
      (hX.tmemPairResult.snoc_not_wr fun _ _ _ h => by cases h)
      (snocObject_readOk hX.effectValidity hX.tcRead hX.cluster rfl hid
        (by intros; simp) (by intros; simp) (by intros; simp))
      (snocObject_fenceScOk hX.fenceSc (by intro s h; cases h)
        fun _ _ hb hc => snocObject_baseCausality_old hX.cluster hshape hid hnb hna hb hc)

/-- A ready successful acquire poll of a thread whose last event is released extends the
execution by a counted event. -/
theorem poll_counted_extension (hX : Consistent L K A mem0 X) {g pc parity : Nat}
    {m : Loc} {scope : MbarScope} (hg : g < L.threads) (hne : X.tr g ≠ [])
    (hrel : Released L X g)
    (hasm : ∀ a ∈ A, ∀ {rec : Record Ref}, rec.id = .thread (g, (X.tr g).length) →
      a.wf L mem0 (X.snocObject g ⟨pc, .wait m parity true true scope⟩ (fun _ => none) m rec))
    {t t1 u : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 ⟨pc, .wait m parity true true scope⟩ (some u))
    {before : State} (hstate : stateBefore (X.objects m) (X.objects m).length = some before)
    (hready : before.phase % 2 ≠ parity % 2) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let record : Record Ref := ⟨.thread (g, (X.tr g).length), .pollParity parity true,
    ⟨some {before with observed := true}, some true,
      if 0 < before.phase then some (before.phase - 1) else none⟩, none⟩
  have hneq : (before.phase % 2 != parity % 2) = true := bne_iff_ne.mpr hready
  have hok : RecordOk (stateBefore (X.objects m) (X.objects m).length) record := by
    rw [hstate]
    simp [RecordOk, record, perform, hneq, pure, Except.pure]
  refine ⟨_, poll_consistent hX hg hne hrel hasm hrun hl he (rec := record) rfl rfl rfl hok,
    Execution.le_trans le_snoc (Execution.le_appendObject ..), ?_⟩
  have hs : (X.snocObject g ⟨pc, .wait m parity true true scope⟩ (fun _ => none) m
      record).size L = X.size L + 1 := size_snoc (r := fun _ => none) hX hg rfl
  omega

/-- The record of a failed poll appended at thread `g`'s next index. -/
def failedRecord (X : Execution) (g p : Nat) (before : State) : Record Ref :=
  ⟨.thread (g, (X.tr g).length), .pollParity p false, ⟨some before, some false, none⟩, none⟩

/-- The execution with a failed poll of `m` appended to thread `g`. -/
def failedPoll (X : Execution) (g pc p : Nat) (m : Loc) (acq : Bool) (scope : MbarScope)
    (before : State) : Execution :=
  X.snocObject g ⟨pc, .wait m p false acq scope⟩ (fun _ => none) m (failedRecord X g p before)

/-- A maximal execution stays maximal when a failed poll is appended: the failed poll counts
for nothing, so every extension of the new execution extends the old one. -/
theorem failed_poll_maximal (hmax : Maximal L K A mem0 X) {g pc parity : Nat}
    {m : Loc} {scope : MbarScope} (hg : g < L.threads) (hne : X.tr g ≠ [])
    (hrel : Released L X g)
    (hasm : ∀ a ∈ A, ∀ {rec : Record Ref}, rec.id = .thread (g, (X.tr g).length) →
      a.wf L mem0 (X.snocObject g ⟨pc, .wait m parity false true scope⟩ (fun _ => none) m rec))
    {t t1 u : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 ⟨pc, .wait m parity false true scope⟩ (some u))
    {before : State} (hstate : stateBefore (X.objects m) (X.objects m).length = some before) :
    Maximal L K A mem0 (failedPoll X g pc parity m true scope before) := by
  have hY := poll_consistent hmax.1 hg hne hrel hasm hrun hl he
    (rec := failedRecord X g parity before) rfl rfl rfl
    (by rw [hstate]; simp [RecordOk, failedRecord, perform, pure, Except.pure])
  have hXY : X.le (failedPoll X g pc parity m true scope before) :=
    Execution.le_trans le_snoc (Execution.le_appendObject ..)
  refine ⟨hY, fun Z hZ hYZ => ?_⟩
  have h1 := hmax.2 Z hZ (Execution.le_trans hXY hYZ)
  have h2 := Proof.ExecutionCountedPrefix.size_mono hXY L
  omega

theorem failedPoll_tr {X : Execution} {g pc p : Nat} {m : Loc} {acq : Bool} {scope : MbarScope}
    {before : State} (h : Nat) :
    (failedPoll X g pc p m acq scope before).tr h =
      if h = g then X.tr g ++ [⟨pc, .wait m p false acq scope⟩] else X.tr h := rfl

theorem failedPoll_objects {X : Execution} {g pc p : Nat} {m : Loc} {acq : Bool}
    {scope : MbarScope} {before : State} (l : Loc) :
    (failedPoll X g pc p m acq scope before).objects l =
      if l = m then X.objects m ++ [failedRecord X g p before] else X.objects l := rfl

end
end PTX.Step
