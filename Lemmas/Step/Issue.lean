-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Released
public import Lemmas.Snoc.SnocConsistent
public import Lemmas.Snoc.SnocObjectMemory
public import Lemmas.Snoc.SnocVisibility
public import Lemmas.Snoc.ExtensionSnocFrame
public import Lemmas.Snoc.PlainAsyncExtend
public import Lemmas.Snoc.SnocBlockingConsistent
public import Lemmas.Snoc.SnocExit
public import Lemmas.Tcgen05.TcExtend
public import Lemmas.Tmem.TmemPairExtend
public import Lemmas.MBarrier.BarExtend
public import Lemmas.Flow.Machine
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Snoc.SnocOldCausality

@[expose] public section

/-! # Appending a thread's next event

A proof tool. A thread whose last event is released can perform an event that adds no waiting edge
out of an existing event (`Kind.WaitFree`), reads and writes no memory and is no shuffle, exit,
lane-value collective, matrix instruction or atomic: in a safe prefix (no race, no mixed-size
conflict) the execution with it appended is consistent once the event's own non-memory
obligations hold (`snoc_counted_extension`). A plain event that uses no mbarrier object and no
Tensor Core discharges those itself (`quiet_counted_extension`): fences, CLC response queries,
bulk commits, the exit, undefined behaviour. A plain event outside the asynchronous instructions
needs no safety at all (`plain_counted_extension`): a store without release semantics, the exit.
The issue of a copy (a tensor load or store, a linear copy) is appended in a safe prefix
(`issue_counted_extension`); its effects are separate steps. A cluster barrier operation and a
named barrier arrival are appended without safety premises (`cluster_counted_extension`,
`bar_counted_extension`), and so is the undefined behaviour of a dead thread
(`dead_counted_extension`). The Tensor Core instructions are appended in `Lemmas.Step.TcLoad`.

Safety of the prefix is used only to order the conflicting pairs at the bytes that are read.
Each `_reads` variant takes that order (`ReadsOrdered`) in its place and carries the proof; it
leaves the identical-value write pairs, which `Race` exempts, unordered, and an append adds no
order between two old accesses (`modelCausality_snoc_old_of`). The safe-prefix statement is
derived from it (`ReadsOrdered.of_safe`). -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution} {mem0 : Mem0} {g : Nat}

/-- An appended event other than an mbarrier initialization, arrival, poll or invalidation
makes no object action. -/
theorem objectAction_snoc_new {e : Event} {r : Nat → Option Ref}
    (hi : ∀ m c, e.kind ≠ .mbInit m c) (ha : ∀ m tx c rel s, e.kind ≠ .arrive m tx c rel s)
    (hw : ∀ m p ok acq s, e.kind ≠ .wait m p ok acq s) (hv : ∀ m, e.kind ≠ .mbInval m)
    (haa : ∀ m, e.kind ≠ .asyncArrive m false) (l : Loc) :
    objectAction (X.snoc g e r) X.async l (.thread (g, (X.tr g).length)) = none := by
  simp only [objectAction, snoc_get_new]
  obtain ⟨pc, k⟩ := e
  cases k
  case mbInit m c => exact absurd rfl (hi m c)
  case arrive m tx c rel s => exact absurd rfl (ha m tx c rel s)
  case wait m p ok acq s => exact absurd rfl (hw m p ok acq s)
  case mbInval m => exact absurd rfl (hv m)
  case asyncArrive m noinc =>
    cases noinc
    · exact absurd rfl (haa m)
    · rfl
  all_goals rfl

/-- An appended event that adds no waiting edge (`Kind.WaitFree`) and is no shuffle, lane-value
collective or matrix instruction is ready if it has returned: a blocking one has not returned
while it is the last event of its thread, and a poll is ready (`ready_of_wait`). -/
theorem snoc_new_ready {e : Event} {r : Nat → Option Ref} (hw : e.kind.WaitFree)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false) :
    Returned (X.snoc g e r) (X.newId g) → Ready L (X.snoc g e r) (X.newId g) := by
  intro h
  have hget : (X.snoc g e r).get (X.newId g) = some e := snoc_get_new
  unfold Returned at h
  rw [hget] at h
  obtain ⟨pc, k⟩ := e
  have hlen : ¬ (X.newId g).2 + 1 < ((X.snoc g ⟨pc, k⟩ r).tr (X.newId g).1).length := by
    simp [snoc_len]
  cases k
  case wait m q ok acq sc => exact ready_of_wait hget
  case shfl => exact (hns _ _ _ _ _ _ rfl).elim
  case tc t => exact (hw.notTc t rfl).elim
  case elect => exact hw.ordinary.elim
  case warpBar => exact hw.ordinary.elim
  case setMaxReg => exact hw.ordinary.elim
  case matrix => simp [isMatrix] at hmat
  all_goals first
    | (simp [Kind.laneValue] at hlv; done)
    | (simp only [Kind.resume] at h; exact (hlen h).elim)
    | simp [Kind.resume] at h

/-- **A released thread performs an event that adds no waiting edge and touches no memory**,
given its non-memory obligations: a counted extension of a prefix whose conflicts at read bytes
are ordered. -/
theorem snoc_counted_extension_reads (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X)
    (hg : g < L.threads) (hrel : Released L X g) {t t1 : TState} {e : Event}
    {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) (he : EStep K A L g t1 e o)
    (hw : e.kind.WaitFree) (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hx : e.kind ≠ .exit) (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new) (hcnt : e.counts = true)
    (htma : TmaOk (X.snoc g e (fun _ => none)))
    (hextra : ExtensionObligations L A (X.snoc g e (fun _ => none)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e (fun _ => none)) x f ↔ baseCausality L X x f) :=
    baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf)
      (fun mask inst h => by have := hw.ordinary; rw [h] at this; exact this) hnb hna
      (fun s h => by have := hw.ordinary; rw [h] at this; exact this)
  refine ⟨_, consistent_snoc_collective_reads hX hord hg hrun hl he hns
    (fun h => by rw [hmat] at h; cases h) hrel.ready (snoc_new_ready hw hns hlv hmat)
    (fun _ _ _ hv => (snoc_memReads_control hX.effectValidity hw.notTc hrd hrmw).mp hv)
    (fun _ _ _ => snoc_memWrites_control hX.effectValidity hwr hrmw)
    (fun _ _ _ hv => modelCausality_snoc_mono hX.tma.2.1 hv)
    (fun _ _ _ _ _ _ hv hf h => byteCausality_snoc_old_of hbo hX.effectValidity
      (refPresent_issuer_lt hX.effectValidity hv) (refPresent_issuer_lt hX.effectValidity hf) h)
    (snoc_plain_orderOk hX hw hns hx hlv hmat hna fun a old new h => absurd h (hrmw a old new))
    hsg hasm htma hextra, le_snoc, ?_⟩
  rw [size_snoc hX hg hcnt]
  omega

/-- `snoc_counted_extension_reads` for a safe prefix. -/
theorem snoc_counted_extension (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X)
    (hr : ¬ Race L X) (hst : StrongOrdered L X) (hg : g <
      L.threads) (hrel : Released L X g) {t t1 : TState} {e : Event}
    {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) (he : EStep K A L g t1 e o)
    (hw : e.kind.WaitFree) (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hx : e.kind ≠ .exit) (hlv : e.kind.laneValue = false) (hmat : isMatrix e = false)
    (hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new) (hcnt : e.counts = true)
    (htma : TmaOk (X.snoc g e (fun _ => none)))
    (hextra : ExtensionObligations L A (X.snoc g e (fun _ => none)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  snoc_counted_extension_reads hX (.of_safe hm hr hst) hg hrel hrun hl he hw hns hx hlv hmat hna
    hnb hrd hwr hrmw hcnt htma hextra hasm hsg

/-- **A released thread performs a plain event outside the asynchronous instructions**: a
counted extension. An exit is appended to a thread that has not exited (its run leaves a
state). -/
theorem plain_counted_extension (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g) {t t1 : TState} {e : Event}
    {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hp : e.kind.Plain) (hk : e.kind.isTma = false)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    (hcnt : e.counts = true)
    (hres : Tmem.Pair.ResultOk L (X.snoc g e (fun _ => none)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hnb : ∀ id count mode, e.kind ≠ .bar id count mode := by
    intro id count mode h
    rw [h] at hp
    exact hp
  have hmat : isMatrix e = false := by
    obtain ⟨pc, k⟩ := e
    cases k <;> first | rfl | simp [Kind.isTma] at hk
  have hcp : ∀ s, e.kind ≠ .copy s := fun s h => by rw [h] at hk; cases hk
  have hextra : ExtensionObligations L A (X.snoc g e (fun _ => none)) := by
    by_cases hx : e.kind = .exit
    · exact ExtensionObligations.snoc_exit hX hx (no_exit_of_run hrun) hne
    · exact ExtensionObligations.snoc_plain hX hp hne hx hrmw hmat hcp hres
  refine ⟨X.snoc g e (fun _ => none), ?_, le_snoc, ?_⟩
  · refine consistent_snoc_plain hX hg hrun hl he hk hnb hns
      (fun a old new h => absurd h (hrmw a old new)) hrel.ready ?_ hextra hasm
    intro a bs h
    rcases h with ⟨pc, hq⟩ | ⟨nw, pc, hq⟩ <;> rw [snoc_get_new] at hq
    · exact absurd (congrArg Event.kind (Option.some.inj hq)) (hrd a bs)
    · exact absurd (congrArg Event.kind (Option.some.inj hq)) (hrmw a bs nw)
  · rw [size_snoc hX hg hcnt]
    omega

/-- **A released thread performs a plain event that uses no mbarrier object and no Tensor
Core**: a counted extension of a prefix whose conflicts at read bytes are ordered. -/
theorem quiet_counted_extension_reads (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X)
    (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g)
    {t t1 : TState} {e : Event} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) (he : EStep K A L g t1 e o)
    (hp : e.kind.Plain) (hk : ∀ k, e.kind ≠ .tc k)
    (hobj : ∀ l, objectAction (X.snoc g e (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = none)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new) (hmat : isMatrix e = false)
    (hcp : ∀ s, e.kind ≠ .copy s) (hcnt : e.counts = true)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hres : Tmem.Pair.ResultOk L (X.snoc g e (fun _ => none)) :=
    hX.tmemPairResult.snoc_not_wr fun _ _ _ h => hwr _ _ (congrArg Event.kind h)
  by_cases hx : e.kind = .exit
  · exact plain_counted_extension hX hg hne hrel hrun hl he hp (by rw [hx]; rfl) hns hrd hrmw
      hcnt hres hasm
  have hw : e.kind.WaitFree := by
    refine ⟨?_, hk⟩
    obtain ⟨pc, k⟩ := e
    cases k
    case fence sem sc => cases sem <;> simp_all [Kind.Ordinary, Kind.Plain]
    all_goals simp_all [Kind.Ordinary, Kind.Plain]
  have hna : ∀ m tx count sc, e.kind ≠ .arrive m tx count true sc := by
    intro m tx count sc h
    rw [h] at hp
    exact Bool.noConfusion hp
  exact snoc_counted_extension_reads hX hord hg hrel hrun hl he hw hns hx hp.quiet.laneValue hmat
    hna (fun id count mode h => by rw [h] at hp; exact hp) hrd hwr hrmw hcnt
    (hX.tmaOk_snoc_unobserved hk hobj)
    (ExtensionObligations.snoc_plain hX hp hne hx hrmw hmat hcp hres) hasm hsg

/-- `quiet_counted_extension_reads` for a safe prefix. -/
theorem quiet_counted_extension (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X)
    (hr : ¬ Race L X) (hst : StrongOrdered L X) (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g)
    {t t1 : TState} {e : Event} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) (he : EStep K A L g t1 e o)
    (hp : e.kind.Plain) (hk : ∀ k, e.kind ≠ .tc k)
    (hobj : ∀ l, objectAction (X.snoc g e (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = none)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hrmw : ∀ a old new, e.kind ≠ .rmw a old new) (hmat : isMatrix e = false)
    (hcp : ∀ s, e.kind ≠ .copy s) (hcnt : e.counts = true)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  quiet_counted_extension_reads hX (.of_safe hm hr hst) hg hne hrel hrun hl he hp hk
    hobj hns hrd hwr hrmw hmat hcp hcnt hasm hsg

/-- An appended copy issue keeps the reduction values: its own effects are still empty, since
every nonempty effect record belongs to an issue of `X`. -/
theorem _root_.PTX.TensorStore.ReduceOk.snoc_issue {e : Event} {r : Nat → Option Ref}
    (hX : Consistent L K A mem0 X) : TensorStore.ReduceOk A (X.snoc g e r) := by
  refine hX.reduce.of_tensorStores rfl fun i s red j hY hw hperf => ⟨?_, rfl⟩
  obtain ⟨pc, hp⟩ := hY
  by_cases hi : i = (g, (X.tr g).length)
  · subst hi
    obtain ⟨s', hs', -⟩ := hX.tma.1 _ ⟨.write (.elem j), hperf⟩
    obtain ⟨pc', hb⟩ := issuedBy_some.mp hs'
    exact absurd (len_of_get hb) (by simp)
  · rw [snoc_get, ite_eq_right hi] at hp
    exact ⟨pc, hp⟩

/-- **A released thread issues a tensor copy, a tensor store or a linear copy**: the copy's
effects are independent observations, none at issue, so the issue is a counted extension of a
prefix whose conflicts at read bytes are ordered. -/
theorem issue_counted_extension_reads (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X)
    (hg : g < L.threads) (hne : X.tr g ≠ []) (hrel : Released L X g)
    {t t1 : TState} {e : Event} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) (he : EStep K A L g t1 e o)
    (hk : (∃ a s, e.kind = .tensorIssue a s) ∨ (∃ a s, e.kind = .tensorStore a s) ∨
      ∃ s, e.kind = .copy s)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨pc, k⟩ := e
  rcases hk with ⟨a, s, rfl⟩ | ⟨a, s, rfl⟩ | ⟨s, rfl⟩
  all_goals
    exact snoc_counted_extension_reads hX hord hg hrel hrun hl he
      (Kind.WaitFree.mk trivial (fun _ h => by cases h))
      nofun nofun rfl rfl nofun nofun nofun nofun nofun rfl
      (hX.tmaOk_snoc_unobserved (fun _ h => by cases h)
        (objectAction_snoc_new (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
          (fun _ _ _ _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)))
      (.snoc_frame_of hX nofun nofun nofun (ClcOk.snoc hX.clc (.inl hne) nofun)
        (hX.tmemPairResult.snoc_not_wr nofun)
        (hX.tcRead_snoc nofun nofun nofun nofun nofun)
        (hX.atomic.snoc hX.store hX.tma.1 nofun)
        (hX.fenceSc_snoc nofun nofun nofun nofun)
        (hX.matrix.snoc rfl) (TensorStore.ReduceOk.snoc_issue hX))
      hasm hsg

/-- `issue_counted_extension_reads` for a safe prefix. -/
theorem issue_counted_extension (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X)
    (hr : ¬ Race L X) (hst : StrongOrdered L X) (hg : g < L.threads) (hne : X.tr g ≠
      []) (hrel : Released L X g)
    {t t1 : TState} {e : Event} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) (he : EStep K A L g t1 e o)
    (hk : (∃ a s, e.kind = .tensorIssue a s) ∨ (∃ a s, e.kind = .tensorStore a s) ∨
      ∃ s, e.kind = .copy s)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g e (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  issue_counted_extension_reads hX (.of_safe hm hr hst) hg hne hrel hrun hl he hk
    hasm hsg

/-- **A released thread in a dead state performs its undefined behaviour.** -/
theorem dead_counted_extension (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ []) (hrel : Released L X g)
    (hasm : ∀ pc f, ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .ub f⟩ (fun _ => none)))
    {u : TState} (hrun : Run K A L g {} (X.tr g) (some u))
    (hd : Flow.Machine.Dead (K := K) (A := A) (L := L) (g := g) u) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨t, f, hl, hf⟩ := hd
  exact plain_counted_extension hX hg (.inl hne) hrel hrun hl (o := none)
    (e := ⟨t.pc, .ub f⟩) ⟨_, hf, by simp [Fires]⟩
    trivial rfl nofun nofun nofun rfl (hX.tmemPairResult.snoc_not_wr fun _ _ _ h => by cases h)
    (hasm t.pc f)

/-- **A released thread performs a cluster barrier operation.** The appended operation has not
returned while it is the last event of its thread. -/
theorem cluster_counted_extension (hX : Consistent L K A mem0 X) {pc : Nat} {op : ClusterOp}
    (hg : g < L.threads) (hne : X.tr g ≠ []) (hrel : Released L X g)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .cluster op⟩ (fun _ => none)))
    {t t1 : TState} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 ⟨pc, .cluster op⟩ o) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hc : (⟨pc, .cluster op⟩ : Event).kind.Control := .inr (.inr ⟨op, rfl⟩)
  have hextra : ExtensionObligations L A (X.snoc g ⟨pc, .cluster op⟩ (fun _ => none)) :=
    ExtensionObligations.snoc_frame hX nofun nofun nofun (hX.clc.snoc (.inl hne) nofun)
      (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc nofun nofun nofun nofun nofun)
      (hX.atomic.snoc hX.store hX.tma.1 nofun) (hX.fenceSc_snoc nofun nofun nofun nofun)
      (hX.matrix.snoc rfl) (fun _ h => Kind.noConfusion h)
  have hY : Consistent L K A mem0 (X.snoc g ⟨pc, .cluster op⟩ (fun _ => none)) :=
    consistent_snoc_preserving hX hg hrun hl he (Control.not_shfl hc) (fun h => by cases h)
      hrel.ready
      (fun h => by
        unfold Returned at h
        rw [snoc_get_new] at h
        simp [Kind.resume, snoc_len] at h)
      (fun v a bs => (Control.memReads hc hX v a bs).mp)
      (fun v a bs => Control.memWrites hc hX v a bs)
      (fun l v f hf => Control.modelCausality hc hX l v f hf)
      (Control.orderOk hc hX) hasm
      (hX.tmaOk_snoc_unobserved (by intro k h; cases h)
        fun _ => by simp only [objectAction, snoc_get_new])
      hextra
  refine ⟨_, hY, le_snoc, ?_⟩
  rw [size_snoc hX hg rfl]
  omega

/-- **A released thread arrives on a named barrier.** -/
theorem bar_counted_extension (hX : Consistent L K A mem0 X) {id : Nat} {count : Option Nat}
    (hg : g < L.threads) (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g)
    {t t1 : TState} {o : Option TState}
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨t1.pc, .bar id count⟩ (fun _ => none)))
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 ⟨t1.pc, .bar id count⟩ o) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g ⟨t1.pc, .bar id count⟩ (fun _ => none)) x f ↔
        baseCausality L X x f) :=
    baseCausality_snoc_old_bar hX.cluster hX.rf hX.ctaBar hg rfl
  have hY : Consistent L K A mem0 (X.snoc g ⟨t1.pc, .bar id count⟩ (fun _ => none)) :=
    consistent_bar_snoc hX hg hrun hl he hrel.ready
      (.snoc_quiet hX trivial hne nofun
        (hX.tmemPairResult.snoc_not_wr fun _ _ _ h => by cases h)
        (readOk_snoc hX.tcRead hX.tcCommit hX.tma.2.2.1 hX.tma.2.1 hbo
          (fun _ _ _ _ h => by cases h))
        (hX.atomic.snoc hX.store hX.tma.1 nofun)
        (hX.fenceSc.snoc nofun fun _ _ hb h => (hbo hb).mp h)
        (hX.matrix.snoc rfl) (hX.reduce.snoc fun _ h => Kind.noConfusion h))
      hasm
  refine ⟨_, hY, le_snoc, ?_⟩
  rw [size_snoc hX hg rfl]
  omega

end
end PTX.Step
