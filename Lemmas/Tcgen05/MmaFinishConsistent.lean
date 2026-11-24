-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.MmaFinish
public import Lemmas.Execution.NeedFills
public import Lemmas.Order.WaitingClosure
public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Async.AsyncExecution
public import Lemmas.Tcgen05.MmaCompletionFrame
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc

@[expose] public section

section
/-! New MMA read/completion stages lead only forward within that operation and publish no
mbarrier notification, so completing an MMA is a sink frame of the execution order
(`finishMma_sinkFrame`). -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {values : MmaOperands}
  {ra rb : Nat → Option Ref}

def MmaPart : Part → Prop
  | .mmaRead _ _ | .mmaDone => True
  | _ => False

def MmaRef (i : EvId) (e : Ref) : Prop := ∃ p, e = .async i p ∧ MmaPart p

def mmaNodeRank (p : Part) (b : Bool) : Nat :=
  (if p = .mmaDone then 2 else 0) + if b then 1 else 0

theorem no_mma_object_before (ho : ObjectsOk X) {p : Part} (hp : MmaPart p)
    {loc : Loc} {f : Ref} : ¬ Before (X.objects loc) (.async i p) f := by
  rintro ⟨j, k, r, s, hj, hid, _⟩
  have hm := ((ho loc).2.1 r (List.mem_of_getElem? hj)).1
  cases p <;> simp only [MmaPart] at hp
  all_goals simp [objectAction, hid] at hm

theorem finishMma_present_old {e : Ref} (he : ¬ MmaRef i e) :
    (X.finishMma i values ra rb).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    by_cases hj : j = i
    · subst j
      cases p <;> try rfl
      all_goals exact (he ⟨_, rfl, True.intro⟩).elim
    · cases p <;> simp only [Execution.RefPresent, Execution.AsyncPresent,
        Execution.MmaRead,
        Execution.finishMma, ite_eq_right hj]
      all_goals rfl

/-- No record of an object is an MMA node. -/
theorem record_not_mma (ho : ObjectsOk X) {m : Loc} {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects m) {j : EvId} {p : Part} (hp : MmaPart p) : r.id ≠ .async j p := by
  intro hid
  have hm := ((ho m).2.1 r hr).1
  cases p <;> simp only [MmaPart] at hp
  all_goals simp [objectAction, hid] at hm

theorem groupWaitStages_not_mma (X : Execution) (j : EvId) (k : GroupWait) {p : Part}
    (hp : p ∈ GroupWaitStages X j k) : ¬ MmaPart p := by
  unfold GroupWaitStages at hp
  split at hp <;> simp at hp <;> rcases hp with rfl | rfl <;> simp [MmaPart]

/-- No need of a thread instruction is filled by an MMA node: the needs fill thread nodes, group
wait stages and recorded object updates, none of which is an MMA stage. -/
theorem needs_node_not_mma (ho : ObjectsOk X) {j : EvId} {fills : Ref → Prop}
    (hn : Need.node fills ∈ Needs L X j) {p : Part} (hp : MmaPart p) {a : EvId} :
    ¬ fills (.async a p) := by
  intro hf
  rcases needs_node_cases hn hf with ⟨t, h⟩ | ⟨a', k, q, h, hq⟩ | ⟨m, r, hr, h⟩
  · cases h
  · cases h
    exact groupWaitStages_not_mma X _ _ hq hp
  · exact record_not_mma ho hr hp h.symm

/-- The needs of an event are those of the execution before the MMA completes. -/
theorem finishMma_needs (ho : ObjectsOk X) (j : EvId) :
    Needs L (X.finishMma i values ra rb) j = Needs L X j := by
  refine needs_congr (L := L) (X := X) (Y := X.finishMma i values ra rb) (fun _ => rfl)
    (fun k e hk => ?_) (fun e m => ?_) j
  · cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl)
  · refine pollNeeds_congr (X := X) (Y := X.finishMma i values ra rb) (fun _ => rfl)
      (fun m r hr w => ?_) e m
    exact and_congr (finishMma_present_old fun ⟨q, he, hq⟩ => record_not_mma ho hr hq he)
      Iff.rfl

theorem witness_not_mma (ho : ObjectsOk X) {p : Part} (hp : MmaPart p) {j : EvId} :
    ¬ Witness L (X.finishMma i values ra rb) (.async i p) j := by
  rintro ⟨fills, hn, -, hf⟩
  rw [finishMma_needs ho] at hn
  exact needs_node_not_mma ho hn hp hf

theorem finishMma_waits_from_mma (ho : ObjectsOk X) (hm : AsyncCopy.CommitOk X)
    (hn : X.async.mmaDone i = false) {p : Part} (hp : MmaPart p)
    {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.finishMma i values ra rb) (.async i p, b) v) :
    ∃ q c, v = (.async i q, c) ∧ MmaPart q ∧ mmaNodeRank p b < mmaNodeRank q c := by
  rcases h with ⟨he, hb, hb', _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨hb, hb', ha⟩ | ⟨_, _, loc, ho'⟩ | ⟨j, k, he, _⟩ | ⟨_, _, j, hf, hw⟩ |
    ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨_, _, j, k, he, _⟩ | ⟨_, _, hi⟩
  · exact ⟨p, true, Prod.ext he.symm hb', hp, by simp [mmaNodeRank, hb]⟩
  · cases he
  · cases he
  · cases he
  · cases he
  · replace ha : StageEdge (X.finishMma i values ra rb) (.async i p) v.1 := by
      rcases ha with ⟨-, h0, -⟩ | ⟨-, -, h⟩
      · exact absurd h0 (by simp [hb])
      · exact h
    cases p <;> simp only [MmaPart] at hp
    all_goals try cases hp
    all_goals cases hv : v.1 with
    | thread j => rw [hv] at ha; exact False.elim ha
    | async j q =>
      rw [hv] at ha
      cases q <;> try exact False.elim ha
      all_goals first
        | (have hd := (hm j _ ha.2.2).2 i ha.1; rw [hn] at hd; cases hd)
        | (obtain ⟨rfl, _⟩ := ha
           refine ⟨_, false, Prod.ext hv hb', ?_, ?_⟩
           · trivial
           · simp [mmaNodeRank, hb])
  · exact (no_mma_object_before ho hp ho').elim
  · cases he
  · exact (witness_not_mma ho hp hw).elim
  · cases he
  · cases he
  · cases he
  · cases he
  · cases he
  · obtain ⟨_, _, k, q, he, _⟩ := hi
    cases he

theorem finishMma_stageEdge_old {e f : Ref} (he : ¬ MmaRef i e) (hf : ¬ MmaRef i f)
    (h : StageEdge (X.finishMma i values ra rb) e f) : StageEdge X e f := by
  cases e with
  | thread j => exact h.elim
  | async j p =>
    cases f with
    | thread k => cases p <;> exact h.elim
    | async k q =>
      cases p <;> cases q <;> try exact False.elim h
      all_goals first
        | exact h
        | exact ⟨h.1, (finishMma_present_old he).mp h.2.1, (finishMma_present_old hf).mp h.2.2⟩

theorem finishMma_stageOrder_old {e f : Ref} {b b' : Bool} (he : ¬ MmaRef i e) (hf : ¬ MmaRef i f)
    (h : StageOrder (X.finishMma i values ra rb) (e, b) (f, b')) : StageOrder X (e, b) (f, b') :=
  h.imp (fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, (finishMma_present_old he).mp h4⟩)
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, finishMma_stageEdge_old he hf h3⟩

theorem finishMma_issueStage_old {e f : Ref} {b b' : Bool} (hf : ¬ MmaRef i f)
    (h : IssueStage (X.finishMma i values ra rb) (e, b) (f, b')) : IssueStage X (e, b) (f, b') := by
  obtain ⟨h1, h2, j, p, he, hfe, hr, hp, hm⟩ := h
  subst hfe
  exact ⟨h1, h2, j, p, he, rfl, by subst he; exact hr, (finishMma_present_old hf).mp hp, hm⟩

theorem finishMma_witness_old (ho : ObjectsOk X) {e : Ref} {j : EvId} (he : ¬ MmaRef i e)
    (h : Witness L (X.finishMma i values ra rb) e j) : Witness L X e j := by
  obtain ⟨fills, hn, hx, hf⟩ := h
  rw [finishMma_needs ho] at hn
  exact ⟨fills, hn, (finishMma_present_old he).mp hx, hf⟩

/-- The rank of an MMA node. -/
def mmaRank : Ref × Bool → Nat
  | (.async _ p, b) => mmaNodeRank p b
  | _ => 0

/-- The new MMA stages only lead forward within that operation and are recorded in no object.
Outside the operation every order relation is old. -/
theorem finishMma_sinkFrame {K : Kernel} {A : List Assumption} (ho : ObjectsOk X)
    (hm : AsyncCopy.CommitOk X) (hn : X.async.mmaDone i = false) (hX : OrderOk L K A X) :
    SinkFrame L K A X (X.finishMma i values ra rb) (fun n => MmaRef i n.1) := by
  have hclosed : ∃ rank : Ref × Bool → Nat, ∀ u v, Waits L (X.finishMma i values ra rb) u v →
      MmaRef i u.1 → MmaRef i v.1 ∧ rank u < rank v := by
    refine ⟨mmaRank, fun u v h hu => ?_⟩
    obtain ⟨p, he, hp⟩ := hu
    obtain ⟨e, b⟩ := u
    simp only at he
    subst he
    obtain ⟨q, c, rfl, hq, hlt⟩ := finishMma_waits_from_mma ho hm hn hp h
    exact ⟨⟨q, rfl, hq⟩, hlt⟩
  have hcause : ∀ u v, ¬ MmaRef i u.1 → ¬ MmaRef i v.1 →
      stageCausality L (X.finishMma i values ra rb) u v →
      Relation.TransGen (stageCausality L X) u v := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ hu hv hc
    rcases hc with hc | ⟨h1, h2, j, k, h3, h4, hc⟩ | ⟨h1, h2, k, h3, hc⟩
    · exact .single (.inl (finishMma_stageOrder_old hu hv hc))
    · exact .single (.inr (.inl ⟨h1, h2, j, k, h3, h4, hc⟩))
    · exact .single (.inr (.inr ⟨h1, h2, k, h3, hc⟩))
  exact {
  closed := hclosed
  cause := hcause
  observed := by
    intro x w hx hw h
    rcases h with ⟨ho', j, m, pc, q, ws, us, g, h1, h2, h3, h4⟩ | ⟨i', p, j, k, h1, h2, h3, h4, h5⟩
    · exact .inl ⟨⟨(finishMma_present_old hx).mp ho'.1, ho'.2⟩, j, m, pc, q, ws, us, g, h1, h2, h3,
        h4⟩
    · subst h1
      exact .inr ⟨i', p, j, k, rfl, h2, (finishMma_present_old hx).mp h3, h4, h5⟩
  object := fun _ _ _ _ _ h => h
  objectSync := fun _ _ _ _ _ h => h
  dep := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ hu hv hc
    rcases hc with hc | hc | ⟨h1, h2, j, hj, hw⟩ | hc
    · exact .single (.inl (finishMma_stageOrder_old hu hv hc))
    · exact .single (.inr (.inl (finishMma_issueStage_old hv hc)))
    · exact .single (.inr (.inr (.inl ⟨h1, h2, j, hj, finishMma_witness_old ho hu hw⟩)))
    · exact .single (.inr (.inr (.inr hc)))
  issue := fun _ _ _ _ _ hi => by obtain ⟨_, he, _⟩ := hi; cases he
  asyncSelf := fun m j p y hb => (hX.asyncObject m j p y hb).1
  asyncObserved := fun _ _ _ _ _ _ h => h
  initFence := by
    intro m init w y hsync hpath hb
    obtain ⟨rank, hrank⟩ := hclosed
    have hv : ¬ MmaRef i (.thread y.issuer) := fun ⟨_, he, _⟩ => by cases he
    obtain ⟨-, hp⟩ := SinkFrame.old_path (S := fun n => MmaRef i n.1) hrank
      (fun _ _ => stageCausality.waits) hcause hpath hv
    exact hX.initFence m init w y hsync hp hb
  get := fun _ _ => rfl }

end
end PTX
end

section
namespace PTX
open AsyncCopy
noncomputable section

/-- Completing an MMA changes no read of an atomic operation, so atomicity is kept. -/
theorem finishMma_atomicOk {L : Launch} {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref} (h : AtomicOk L X) : AtomicOk L (X.finishMma i values ra rb) :=
  atomicOk_congr (X := X) (Y := X.finishMma i values ra rb)
    (fun p l n => by cases p <;> exact Iff.rfl) (fun _ _ => Iff.rfl)
    (fun p k => by cases p <;> rfl) h

private theorem consistent_finishTc {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref}
    (hX : Consistent L K A mem0 X)
    (hn : X.async.mmaDone i = false) (hready : TcMma.CompletionReady L X i)
    (heff : TcEffectsOk (X.finishMma i values ra rb))
    (hr : RfWf mem0 (X.finishMma i values ra rb))
    (hf : NoFuture L (X.finishMma i values ra rb))
    (hh : Hidden L (X.finishMma i values ra rb))
    (hread : TcMma.ReadOk L A (X.finishMma i values ra rb))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.finishMma i values ra rb)) :
    Consistent L K A mem0 (X.finishMma i values ra rb) where
  thr := hX.thr
  outside := hX.outside
  rf := hr
  ctaBar := hX.ctaBar
  cluster := hX.cluster
  dependency := by
    have hfr := finishMma_sinkFrame (L := L) (K := K) (A := A) (X := X) (i := i) (values := values)
      (ra := ra) (rb := rb) hX.tma.2.2.1 hX.tcCommit hn hX.orderOk
    refine ⟨?_, fun o ho => hfr.toBase.depAcyclic hX.dependency.acyclic o ho⟩
    intro e hret n hn'
    have hn'' : n ∈ Needs L X e := by
      rw [finishMma_needs (L := L) (i := i) (values := values) (ra := ra) (rb := rb)
        hX.tma.2.2.1] at hn'
      exact hn'
    have hready := hX.dependency.ready e hret n hn''
    cases n with
    | cond holds => exact hready
    | node fills =>
      obtain ⟨x, hx, hf⟩ := hready
      have hno : ¬ MmaRef i x := fun ⟨p, he, hp⟩ =>
        needs_node_not_mma hX.tma.2.2.1 hn'' hp (he ▸ hf)
      exact ⟨x, (finishMma_present_old hno).mpr hx, hf⟩
  shfl := hX.shfl
  vote := hX.vote
  warpValue := hX.warpValue
  matrix := hX.matrix
  elect := hX.elect
  warpBar := hX.warpBar
  observation := ((finishMma_sinkFrame hX.tma.2.2.1 hX.tcCommit hn hX.orderOk).orderOk
    hX.orderOk).observation
  object := ((finishMma_sinkFrame hX.tma.2.2.1 hX.tcCommit hn hX.orderOk).orderOk
    hX.orderOk).object
  asyncObject := ((finishMma_sinkFrame hX.tma.2.2.1 hX.tcCommit hn hX.orderOk).orderOk
    hX.orderOk).asyncObject
  initFence := ((finishMma_sinkFrame hX.tma.2.2.1 hX.tcCommit hn hX.orderOk).orderOk
    hX.orderOk).initFence
  noFuture := hf
  hidden := hh
  tma := ⟨hX.tma.1, heff, hX.tma.2.2⟩
  clc := hX.clc
  tensor := hX.tensor
  store := hX.store
  reduce := hX.reduce.of_tensorStores rfl fun _ _ _ _ hc _ _ => ⟨hc, rfl⟩
  atomic := finishMma_atomicOk hX.atomic
  fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, hX.fenceSc.causal⟩
  tmemPair := hX.tmemPair
  tcCommit := by
    intro c rank hc
    obtain ⟨hs, hd⟩ := hX.tcCommit c rank hc
    refine ⟨hs, ?_⟩
    intro mma hm
    have hh := hd mma hm
    change (if mma = i then true else X.async.mmaDone mma) = true
    split <;> simp_all
  tmemPairCompletion := Tmem.Pair.completionClosed_of_trace rfl rfl rfl hX.tmemPairCompletion
  tmemPairResult := hX.tmemPairResult
  mmaCompletion := TcMma.completionClosed_update
    (X := X) (Y := X.finishMma i values ra rb) (i := i) (fun _ _ _ _ _ => Iff.rfl)
    (fun _ => rfl) hX.mmaCompletion hready
  tcRead := hread
  asm := hasm

/-- Complete an issued MMA after proving the new reads' values and ordering. The
existing thread, object and collective constraints are preserved; the new memory
obligations and optional assumptions remain explicit proof obligations. -/
theorem consistent_finishMma {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref} {d : Nat} {s : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat}
    (hX : Consistent L K A mem0 X) (hi : X.MmaIssue i d s accum mask)
    (hn : X.async.mmaDone i = false) (hready : TcMma.CompletionReady L X i)
    (hv : TcMma.Valid s.descriptor)
    (ha : values.a.length = TcMma.Operand.a.bytes s.descriptor)
    (hb : values.b.length = TcMma.Operand.b.bytes s.descriptor)
    (hr : RfWf mem0 (X.finishMma i values ra rb))
    (hf : NoFuture L (X.finishMma i values ra rb))
    (hh : Hidden L (X.finishMma i values ra rb))
    (hread : TcMma.ReadOk L A (X.finishMma i values ra rb))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.finishMma i values ra rb)) :
    Consistent L K A mem0 (X.finishMma i values ra rb) :=
  consistent_finishTc hX hn hready (finishMma_tcEffectsOk hX.tma.2.1 hi hv ha hb)
    hr hf hh hread hasm

/-- Complete a Tensor Memory copy after proving the new shared reads' values and ordering. -/
theorem consistent_finishCp {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref} {c : TcCopy.Spec}
    (hX : Consistent L K A mem0 X) (hi : X.CpIssue i c)
    (hn : X.async.mmaDone i = false) (hready : TcMma.CompletionReady L X i)
    (ha : values.a.length = c.ctas.length * c.shape.sourceBytes) (hb : values.b = [])
    (hr : RfWf mem0 (X.finishMma i values ra rb))
    (hf : NoFuture L (X.finishMma i values ra rb))
    (hh : Hidden L (X.finishMma i values ra rb))
    (hread : TcMma.ReadOk L A (X.finishMma i values ra rb))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.finishMma i values ra rb)) :
    Consistent L K A mem0 (X.finishMma i values ra rb) :=
  consistent_finishTc hX hn hready (finishCp_tcEffectsOk hX.tma.2.1 hi ha hb)
    hr hf hh hread hasm

private theorem mma_sum_map_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ i ∈ xs, f i ≤ g i) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := h i (by simp)
    have ht := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Arithmetic completion strictly increases counted size, including when operand
reads were already recorded. -/
theorem finishMma_size {L : Launch} {X : Execution} {i : EvId} {values : MmaOperands}
    {ra rb : Nat → Option Ref} (hg : i.1 < L.threads) (hi : i.2 < (X.tr i.1).length)
    (hn : X.async.mmaDone i = false) :
    X.size L < (X.finishMma i values ra rb).size L := by
  have hs : ∀ j, (if j = i then X.asyncSize j + 1 else X.asyncSize j) ≤
      (X.finishMma i values ra rb).asyncSize j := by
    intro j
    have hm : (X.finishMma i values ra rb).async.mmaStarted j =
        if j = i then true else X.async.mmaStarted j := by
      by_cases he : j = i <;> simp [Snapshot.mmaStarted, Execution.finishMma, he]
    have hd : (X.finishMma i values ra rb).async.mmaDone j =
        if j = i then true else X.async.mmaDone j := rfl
    have hel : (X.finishMma i values ra rb).elemSize j = X.elemSize j := rfl
    unfold Execution.asyncSize
    rw [hm, hd, hel, show (X.finishMma i values ra rb).async.copies = X.async.copies from rfl,
      show (X.finishMma i values ra rb).async.arrived = X.async.arrived from rfl,
      show (X.finishMma i values ra rb).clc = X.clc from rfl,
      show (X.finishMma i values ra rb).tensor = X.tensor from rfl,
      show (X.finishMma i values ra rb).tensorStores = X.tensorStores from rfl,
      show (X.finishMma i values ra rb).tcNotified = X.tcNotified from rfl]
    by_cases he : j = i
    · subst j
      simp only [↓reduceIte, hn, Bool.false_eq_true]
      split_ifs <;> omega
    · simp only [he, ↓reduceIte, le_refl]
  let f := fun g => (X.tr g).countP Event.counts +
    ((List.range (X.tr g).length).map fun k => X.asyncSize (g, k)).sum
  have hb : ∀ g, (if g = i.1 then f g + 1 else f g) ≤
      ((X.finishMma i values ra rb).tr g).countP Event.counts +
      ((List.range ((X.finishMma i values ra rb).tr g).length).map
        fun k => (X.finishMma i values ra rb).asyncSize (g, k)).sum := by
    intro g
    have hm := mma_sum_map_mono (List.range (X.tr g).length)
      (fun k => if (g, k) = i then X.asyncSize (g, k) + 1 else X.asyncSize (g, k))
      (fun k => (X.finishMma i values ra rb).asyncSize (g, k)) (fun k _ => hs (g, k))
    by_cases he : g = i.1
    · subst g
      have heq : ∀ k, (i.1, k) = i ↔ k = i.2 := by intro k; exact Prod.ext_iff.trans (by simp)
      simp only [heq] at hm
      rw [sum_range_bump, ite_eq_left hi] at hm
      simpa [f, Execution.finishMma, Nat.add_assoc] using
        Nat.add_le_add_left hm ((X.tr i.1).countP Event.counts)
    · have heq : ∀ k, (g, k) ≠ i := fun k h => he (congrArg Prod.fst h)
      simpa [f, Execution.finishMma, he, heq] using
        Nat.add_le_add_left hm ((X.tr g).countP Event.counts)
  have hm := mma_sum_map_mono (List.range L.threads)
    (fun g => if g = i.1 then f g + 1 else f g) _ (fun g _ => hb g)
  rw [sum_range_bump, ite_eq_left hg] at hm
  change X.threadSize L + 1 ≤ (X.finishMma i values ra rb).threadSize L at hm
  have hp : (X.finishMma i values ra rb).pairSize L = X.pairSize L := rfl
  simp only [Execution.size, hp]
  omega


end
end PTX
end
