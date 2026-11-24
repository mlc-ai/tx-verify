-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Order.WaitOrderWaits
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Async.AsyncCopy

@[expose] public section

namespace PTX

/-! ## Execution-order axioms of an extension

An extension `Y` of `X` adds nodes (and possibly edges into return nodes of blocked
instructions). `S` collects the new nodes and those terminal ones. No `Waits` edge of `Y`
leaves `S`, and a rank grows along the `Waits` edges inside `S`; every relation of
MEM-OBJECT-ORDER-CAUSALITY and of DEP-ORDER is contained in `Waits` paths, so the same holds for
it. Between two nodes outside `S`, each relation of `Y` is one of `X` (the frame). Then each
predicate transfers from `X` to `Y`: a cycle of `Y` either stays outside `S`, where it is a cycle
of `X`, or enters `S` and cannot come back. -/

/-- The execution-order axioms of `Consistent`: MEM-OBJECT-ORDER-CAUSALITY and the acyclicity half
of DEP-ORDER. The readiness half of the dependency axiom (`DependencyOk.ready`) constrains single
events, not the orders, and is not transferred here. -/
structure OrderOk (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) : Prop where
  observation : ObservationCausal L X
  object : ObjectCoherent L X
  asyncObject : AsyncObjectOrdered L X
  /-- DEP-ORDER: no cycle of dependency steps with the order of any one object. -/
  depAcyclic : ∀ o, o.Enabling → ∀ n,
    ¬ Relation.TransGen (fun a c => DepStep L K X a c ∨ ObjectOrder L X o a c) n n
  initFence : InitFenceOrdered L X

theorem Consistent.orderOk {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) : OrderOk L K A X :=
  ⟨hX.observation, hX.object, hX.asyncObject, hX.dependency.acyclic, hX.initFence⟩

/-- `Y` extends `X` by the node set `S`: no `Waits` edge of `Y` leaves `S`, a rank grows
along such edges inside `S`, and outside `S` each order relation of `Y` is one of `X`. -/
structure SinkFrame (L : Launch) (K : Kernel) (A : List Assumption) (X Y : Execution)
    (S : AsyncCopy.Ref × Bool → Prop) : Prop where
  closed : ∃ rank : AsyncCopy.Ref × Bool → Nat,
    ∀ u v, Waits L Y u v → S u → S v ∧ rank u < rank v
  cause : ∀ u v, ¬ S u → ¬ S v → stageCausality L Y u v → Relation.TransGen (stageCausality L X) u v
  observed : ∀ x w, ¬ S (x, false) → ¬ S (w, true) → SyncObserved L Y x w → SyncObserved L X x w
  /-- The recorded order of one object at old nodes is that of `X` (EXT-ASYNC-OBJECT). -/
  object : ∀ o u v, ¬ S u → ¬ S v → ObjectOrder L Y o u v → ObjectOrder L X o u v
  /-- The synchronizing part of one object's order at old nodes is that of `X`
  (MEM-OBJECT-ORDER-CAUSALITY). -/
  objectSync : ∀ o u v, ¬ S u → ¬ S v → SyncObjectOrder L Y o u v → SyncObjectOrder L X o u v
  /-- The dependency steps between old nodes are paths of `X`'s (DEP-ORDER). -/
  dep : ∀ u v, ¬ S u → ¬ S v → DepStep L K Y u v → Relation.TransGen (DepStep L K X) u v
  /-- An asynchronous update recorded on an object whose issue is new is new as well, and
  follows its issue by `Waits` (EXT-ASYNC-OBJECT). -/
  issue : ∀ m i p y, MBarrier.Before (Y.objects m) (.async i p) y → S (.thread i, false) →
    S (.async i p, true) ∧ Relation.TransGen (Waits L Y) (.thread i, false) (.async i p, true)
  /-- EXT-ASYNC-OBJECT, first clause: no later event of the issuing thread is before the update
  in the object's order. It reads the sources of the object's records (`MBarrier.Record`), which
  the frame of the orders does not carry. -/
  asyncSelf : ∀ m i p y, MBarrier.Before (Y.objects m) (.async i p) y →
    ¬ ∃ j, y = .thread j ∧ j.1 = i.1 ∧ j.2 < i.2
  /-- EXT-ASYNC-OBJECT, second clause, premise: the lifetime records of the object and the
  observations of its updates at old nodes are those of `X`. They read the object's record log
  and the polls recorded on it, which the frame of the orders does not carry. -/
  asyncObserved : ∀ m i p y, ¬ S (.async i p, true) → ¬ S (y, true) →
    (MbarLifetimeRecord Y m y ∨
        ∃ j ws, y = .thread j ∧ AsyncCopy.WaitObserves Y (.async i p) j m true ws) →
      (MbarLifetimeRecord X m y ∨
        ∃ j ws, y = .thread j ∧ AsyncCopy.WaitObserves X (.async i p) j m true ws)
  /-- OBJ-MBAR-INIT-PUBLICATION at the old nodes. The init-fence pattern of `InitFenceSync` is
  read off the cluster-barrier simulation (`ClusterBarrier.ArrivalOf`, `ClusterBarrier.WaitOf`),
  whose records the other fields do not frame, so an extension carries it as a hypothesis. -/
  initFence : InitFenceOrdered L Y
  /-- An event whose issue node is old is the event of `X`. -/
  get : ∀ e, ¬ S (.thread e, false) → Y.get e = X.get e

/-- `SinkFrame` without the frame of the Tensor Memory allocator orders: an appended
allocation record adds order edges into lanes that need not be sinks, and their coherence is
shown separately (`Tmem.Pair.objectCoherent_recordEntry`). The other objects are those of
`DependencyOk` (`OrderObject.Enabling`). -/
structure SinkFrame.Base (L : Launch) (K : Kernel) (A : List Assumption) (X Y : Execution)
    (S : AsyncCopy.Ref × Bool → Prop) : Prop where
  closed : ∃ rank : AsyncCopy.Ref × Bool → Nat,
    ∀ u v, Waits L Y u v → S u → S v ∧ rank u < rank v
  cause : ∀ u v, ¬ S u → ¬ S v → stageCausality L Y u v → Relation.TransGen (stageCausality L X) u v
  observed : ∀ x w, ¬ S (x, false) → ¬ S (w, true) → SyncObserved L Y x w → SyncObserved L X x w
  object : ∀ o, o.Enabling → ∀ u v, ¬ S u → ¬ S v → ObjectOrder L Y o u v →
    ObjectOrder L X o u v
  objectSync : ∀ o, o.Enabling → ∀ u v, ¬ S u → ¬ S v → SyncObjectOrder L Y o u v →
    SyncObjectOrder L X o u v
  dep : ∀ u v, ¬ S u → ¬ S v → DepStep L K Y u v → Relation.TransGen (DepStep L K X) u v
  issue : ∀ m i p y, MBarrier.Before (Y.objects m) (.async i p) y → S (.thread i, false) →
    S (.async i p, true) ∧ Relation.TransGen (Waits L Y) (.thread i, false) (.async i p, true)
  asyncSelf : ∀ m i p y, MBarrier.Before (Y.objects m) (.async i p) y →
    ¬ ∃ j, y = .thread j ∧ j.1 = i.1 ∧ j.2 < i.2
  /-- EXT-ASYNC-OBJECT, second clause, premise: the lifetime records of the object and the
  observations of its updates at old nodes are those of `X`. They read the object's record log
  and the polls recorded on it, which the frame of the orders does not carry. -/
  asyncObserved : ∀ m i p y, ¬ S (.async i p, true) → ¬ S (y, true) →
    (MbarLifetimeRecord Y m y ∨
        ∃ j ws, y = .thread j ∧ AsyncCopy.WaitObserves Y (.async i p) j m true ws) →
      (MbarLifetimeRecord X m y ∨
        ∃ j ws, y = .thread j ∧ AsyncCopy.WaitObserves X (.async i p) j m true ws)
  initFence : InitFenceOrdered L Y
  /-- An event whose issue node is old is the event of `X`. -/
  get : ∀ e, ¬ S (.thread e, false) → Y.get e = X.get e

namespace SinkFrame
variable {L : Launch} {K : Kernel} {A : List Assumption} {X Y : Execution}
  {S : AsyncCopy.Ref × Bool → Prop}

/-- The synchronizing part of one object's order is a `Waits` edge: for an mbarrier it keeps the
recorded order, for every other object it is the recorded order. -/
private theorem objectSync_waits {X : Execution} {o : OrderObject} {a c : AsyncCopy.Ref × Bool}
    (h : SyncObjectOrder L X o a c) : Waits L X a c := by
  cases o with
  | mbar m => exact ObjectOrder.waits h.1
  | ctaBar c id => exact ObjectOrder.waits (o := .ctaBar c id) h
  | cluster c => exact ObjectOrder.waits (o := .cluster c) h
  | tmem cta => exact ObjectOrder.waits (o := .tmem cta) h

/-- A path of a relation contained in `Waits` paths stays in `S` once it enters, with growing
rank. -/
theorem closed_path {R : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop}
    {rank : AsyncCopy.Ref × Bool → Nat}
    (hrank : ∀ u v, Waits L Y u v → S u → S v ∧ rank u < rank v)
    (hw : ∀ u v, R u v → Relation.TransGen (Waits L Y) u v) {u v : AsyncCopy.Ref × Bool}
    (h : Relation.TransGen R u v) (hu : S u) : S v ∧ rank u < rank v := by
  have waits : ∀ {a c}, Relation.TransGen (Waits L Y) a c → S a → S c ∧ rank a < rank c := by
    intro a c h ha
    induction h with
    | single h => exact hrank _ _ h ha
    | tail _ h ih =>
      obtain ⟨hb, hab⟩ := ih
      obtain ⟨hc, hbc⟩ := hrank _ _ h hb
      exact ⟨hc, hab.trans hbc⟩
  induction h with
  | single h => exact waits (hw _ _ h) hu
  | tail _ h ih =>
    obtain ⟨hb, hab⟩ := ih
    obtain ⟨hc, hbc⟩ := waits (hw _ _ h) hb
    exact ⟨hc, hab.trans hbc⟩

/-- A path of `Y` ending outside `S` lies outside `S` and maps to a path of `X`. -/
theorem old_path {R R' : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop}
    {rank : AsyncCopy.Ref × Bool → Nat}
    (hrank : ∀ u v, Waits L Y u v → S u → S v ∧ rank u < rank v)
    (hw : ∀ u v, R u v → Relation.TransGen (Waits L Y) u v)
    (hf : ∀ u v, ¬ S u → ¬ S v → R u v → Relation.TransGen R' u v)
    {u v : AsyncCopy.Ref × Bool} (h : Relation.TransGen R u v) (hv : ¬ S v) :
    ¬ S u ∧ Relation.TransGen R' u v := by
  induction h with
  | single h =>
    have hu : ¬ S _ := fun hu => hv (closed_path hrank hw (.single h) hu).1
    exact ⟨hu, hf _ _ hu hv h⟩
  | tail _ h ih =>
    have hb : ¬ S _ := fun hb => hv (closed_path hrank hw (.single h) hb).1
    obtain ⟨hu, p⟩ := ih hb
    exact ⟨hu, p.trans (hf _ _ hb hv h)⟩

/-- No cycle of a relation contained in `Waits` paths enters `S`; outside `S` it is a cycle
of `X`. -/
theorem acyclic {R R' : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop}
    {rank : AsyncCopy.Ref × Bool → Nat}
    (hrank : ∀ u v, Waits L Y u v → S u → S v ∧ rank u < rank v)
    (hw : ∀ u v, R u v → Relation.TransGen (Waits L Y) u v)
    (hf : ∀ u v, ¬ S u → ¬ S v → R u v → Relation.TransGen R' u v)
    (hold : ∀ n, ¬ Relation.TransGen R' n n) : ∀ n, ¬ Relation.TransGen R n n := by
  intro n h
  classical
  by_cases hn : S n
  · exact Nat.lt_irrefl _ (closed_path hrank hw h hn).2
  · exact hold n (old_path hrank hw hf h hn).2

theorem objectCoherent (hf : SinkFrame L K A X Y S) (hX : ObjectCoherent L X) :
    ObjectCoherent L Y := by
  obtain ⟨rank, hrank⟩ := hf.closed
  intro o
  refine acyclic hrank (fun u v h => ?_) (fun u v hu hv h => ?_) (hX o)
  · rcases h with h | h
    · exact stageCausality.waits h
    · exact .single (objectSync_waits h)
  · rcases h with h | h
    · exact Relation.TransGen.mono (fun _ _ => Or.inl) _ _ (hf.cause u v hu hv h)
    · exact .single (.inr (hf.objectSync o u v hu hv h))

theorem Base.depAcyclic (hf : SinkFrame.Base L K A X Y S)
    (hX : ∀ o, o.Enabling → ∀ n,
      ¬ Relation.TransGen (fun a c => DepStep L K X a c ∨ ObjectOrder L X o a c) n n)
    (o : OrderObject) (ho : o.Enabling) : ∀ n,
    ¬ Relation.TransGen (fun a c => DepStep L K Y a c ∨ ObjectOrder L Y o a c) n n := by
  obtain ⟨rank, hrank⟩ := hf.closed
  refine acyclic hrank (fun u v h => ?_) (fun u v hu hv h => ?_) (hX o ho)
  · rcases h with h | h
    · exact DepStep.waits h
    · exact .single (ObjectOrder.waits h)
  · rcases h with h | h
    · exact Relation.TransGen.mono (fun _ _ => Or.inl) _ _ (hf.dep u v hu hv h)
    · exact .single (.inr (hf.object o ho u v hu hv h))

theorem Base.observationCausal (hf : SinkFrame.Base L K A X Y S) (hX : ObservationCausal L X) :
    ObservationCausal L Y := by
  obtain ⟨rank, hrank⟩ := hf.closed
  intro x w ho hc
  classical
  by_cases hx : S (x, false)
  · obtain ⟨hw, hxw⟩ := closed_path hrank (R := Waits L Y) (fun _ _ h => .single h)
      (SyncObserved.waits ho) hx
    exact Nat.lt_irrefl _ (hxw.trans (closed_path hrank (fun _ _ => stageCausality.waits) hc hw).2)
  · obtain ⟨hw, p⟩ := old_path hrank (fun _ _ => stageCausality.waits) hf.cause hc hx
    exact hX x w (hf.observed x w hx hw ho) p

theorem Base.asyncObjectOrdered (hf : SinkFrame.Base L K A X Y S) (hX : AsyncObjectOrdered L X) :
    AsyncObjectOrdered L Y := by
  obtain ⟨rank, hrank⟩ := hf.closed
  intro m i p y hb
  have hw : Waits L Y (.async i p, true) (y, true) :=
    ObjectOrder.waits (o := .mbar m) ⟨rfl, rfl, hb⟩
  classical
  refine ⟨hf.asyncSelf m i p y hb, fun hdisj hc => ?_⟩
  by_cases hi : S (.thread i, false)
  · obtain ⟨hn, hin⟩ := hf.issue m i p y hb hi
    obtain ⟨hy, hny⟩ := hrank _ _ hw hn
    have h1 := (closed_path hrank (fun _ _ => stageCausality.waits) hc hy).2
    have h2 := (closed_path hrank (R := Waits L Y) (fun _ _ h => .single h) hin hi).2
    omega
  · obtain ⟨hy, p'⟩ := old_path hrank (fun _ _ => stageCausality.waits) hf.cause hc hi
    have hn : ¬ S (.async i p, true) := fun hn => hy (hrank _ _ hw hn).1
    obtain ⟨-, -, hb'⟩ := hf.object (.mbar m) trivial _ _ hn hy ⟨rfl, rfl, hb⟩
    exact (hX m i p y hb').2 (hf.asyncObserved m i p y hn hy hdisj) p'

/-- The objects of `DependencyOk` stay coherent with causality. -/
theorem Base.objectCoherent (hf : SinkFrame.Base L K A X Y S) (hX : ObjectCoherent L X)
    (o : OrderObject)
    (ho : o.Enabling) : ∀ n,
    ¬ Relation.TransGen (fun a c => stageCausality L Y a c ∨ SyncObjectOrder L Y o a c) n n := by
  obtain ⟨rank, hrank⟩ := hf.closed
  refine acyclic hrank (fun u v h => ?_) (fun u v hu hv h => ?_) (hX o)
  · rcases h with h | h
    · exact stageCausality.waits h
    · exact .single (objectSync_waits h)
  · rcases h with h | h
    · exact Relation.TransGen.mono (fun _ _ => Or.inl) _ _ (hf.cause u v hu hv h)
    · exact .single (.inr (hf.objectSync o ho u v hu hv h))

/-- A base frame gives the execution-order axioms once the Tensor Memory allocator orders are
coherent. -/
theorem Base.orderOk (hf : SinkFrame.Base L K A X Y S) (hX : OrderOk L K A X)
    (htmem : ∀ cta n, ¬ Relation.TransGen
      (fun a c => stageCausality L Y a c ∨ SyncObjectOrder L Y (.tmem cta) a c) n n) :
    OrderOk L K A Y := by
  refine ⟨hf.observationCausal hX.observation, ?_, hf.asyncObjectOrdered hX.asyncObject,
    ?_, hf.initFence⟩
  · intro o
    cases o with
    | tmem cta => exact htmem cta
    | mbar m => exact hf.objectCoherent hX.object _ trivial
    | ctaBar c id => exact hf.objectCoherent hX.object _ trivial
    | cluster c => exact hf.objectCoherent hX.object _ trivial
  · intro o ho
    cases o with
    | tmem cta => exact ho.elim
    | mbar m => exact hf.depAcyclic hX.depAcyclic _ trivial
    | ctaBar c id => exact hf.depAcyclic hX.depAcyclic _ trivial
    | cluster c => exact hf.depAcyclic hX.depAcyclic _ trivial

theorem toBase (hf : SinkFrame L K A X Y S) : SinkFrame.Base L K A X Y S :=
  ⟨hf.closed, hf.cause, hf.observed, fun o _ => hf.object o, fun o _ => hf.objectSync o,
    hf.dep, hf.issue, hf.asyncSelf, hf.asyncObserved, hf.initFence, hf.get⟩

theorem observationCausal (hf : SinkFrame L K A X Y S) (hX : ObservationCausal L X) :
    ObservationCausal L Y :=
  hf.toBase.observationCausal hX

theorem asyncObjectOrdered (hf : SinkFrame L K A X Y S) (hX : AsyncObjectOrdered L X) :
    AsyncObjectOrdered L Y :=
  hf.toBase.asyncObjectOrdered hX

theorem orderOk (hf : SinkFrame L K A X Y S) (hX : OrderOk L K A X) : OrderOk L K A Y :=
  ⟨hf.observationCausal hX.observation, hf.objectCoherent hX.object,
    hf.asyncObjectOrdered hX.asyncObject, hf.toBase.depAcyclic hX.depAcyclic, hf.initFence⟩

/-- When no issue node is new, no asynchronous update has a new issue. -/
theorem issue_none (h : ∀ i, ¬ S (.thread i, false)) :
    ∀ m i p y, MBarrier.Before (Y.objects m) (.async i p) y → S (.thread i, false) →
      S (.async i p, true) ∧
        Relation.TransGen (Waits L Y) (.thread i, false) (.async i p, true) :=
  fun _ i _ _ _ hi => (h i hi).elim

/-- With no new or terminal node, the frame needs no rank. -/
theorem closed_empty : ∃ rank : AsyncCopy.Ref × Bool → Nat,
    ∀ u v, Waits L Y u v → (fun _ => False) u → (fun _ => False) v ∧ rank u < rank v :=
  ⟨fun _ => 0, fun _ _ _ h => h.elim⟩

/-- The old-node transport of a sink frame. When different orders have different new
edges, their closed sets and ranks can be checked separately. -/
structure Transport (L : Launch) (K : Kernel) (A : List Assumption) (X Y : Execution)
    (S : AsyncCopy.Ref × Bool → Prop) : Prop where
  cause : ∀ u v, ¬ S u → ¬ S v → stageCausality L Y u v → Relation.TransGen (stageCausality L X) u v
  observed : ∀ x w, ¬ S (x, false) → ¬ S (w, true) → SyncObserved L Y x w → SyncObserved L X x w
  /-- The recorded order of one object at old nodes is that of `X` (EXT-ASYNC-OBJECT). -/
  object : ∀ o u v, ¬ S u → ¬ S v → ObjectOrder L Y o u v → ObjectOrder L X o u v
  /-- The synchronizing part of one object's order at old nodes is that of `X`
  (MEM-OBJECT-ORDER-CAUSALITY). -/
  objectSync : ∀ o u v, ¬ S u → ¬ S v → SyncObjectOrder L Y o u v → SyncObjectOrder L X o u v
  /-- The dependency steps between old nodes are paths of `X`'s (DEP-ORDER). -/
  dep : ∀ u v, ¬ S u → ¬ S v → DepStep L K Y u v → Relation.TransGen (DepStep L K X) u v
  /-- An asynchronous update recorded on an object whose issue is new is new as well, and
  follows its issue by `Waits` (EXT-ASYNC-OBJECT). -/
  issue : ∀ m i p y, MBarrier.Before (Y.objects m) (.async i p) y → S (.thread i, false) →
    S (.async i p, true) ∧ Relation.TransGen (Waits L Y) (.thread i, false) (.async i p, true)
  /-- EXT-ASYNC-OBJECT, first clause: no later event of the issuing thread is before the update
  in the object's order. It reads the sources of the object's records (`MBarrier.Record`), which
  the frame of the orders does not carry. -/
  asyncSelf : ∀ m i p y, MBarrier.Before (Y.objects m) (.async i p) y →
    ¬ ∃ j, y = .thread j ∧ j.1 = i.1 ∧ j.2 < i.2
  /-- EXT-ASYNC-OBJECT, second clause, premise: the lifetime records of the object and the
  observations of its updates at old nodes are those of `X`. They read the object's record log
  and the polls recorded on it, which the frame of the orders does not carry. -/
  asyncObserved : ∀ m i p y, ¬ S (.async i p, true) → ¬ S (y, true) →
    (MbarLifetimeRecord Y m y ∨
        ∃ j ws, y = .thread j ∧ AsyncCopy.WaitObserves Y (.async i p) j m true ws) →
      (MbarLifetimeRecord X m y ∨
        ∃ j ws, y = .thread j ∧ AsyncCopy.WaitObserves X (.async i p) j m true ws)
  /-- OBJ-MBAR-INIT-PUBLICATION at the old nodes. The init-fence pattern of `InitFenceSync` is
  read off the cluster-barrier simulation (`ClusterBarrier.ArrivalOf`, `ClusterBarrier.WaitOf`),
  whose records the other fields do not frame, so an extension carries it as a hypothesis. -/
  initFence : InitFenceOrdered L Y
  /-- An event whose issue node is old is the event of `X`. -/
  get : ∀ e, ¬ S (.thread e, false) → Y.get e = X.get e

theorem Transport.sinkFrame (h : Transport L K A X Y S)
    (closed : ∃ rank : AsyncCopy.Ref × Bool → Nat,
      ∀ u v, Waits L Y u v → S u → S v ∧ rank u < rank v) :
    SinkFrame L K A X Y S :=
  ⟨closed, h.cause, h.observed, h.object, h.objectSync, h.dep, h.issue, h.asyncSelf,
    h.asyncObserved, h.initFence, h.get⟩

/-- Restrict a path to old nodes and transport that path. -/
theorem old_path_direct {R R' : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop}
    (hback : ∀ u v, R u v → ¬ S v → ¬ S u)
    (hf : ∀ u v, ¬ S u → ¬ S v → R u v → Relation.TransGen R' u v)
    {u v : AsyncCopy.Ref × Bool} (hp : Relation.TransGen R u v) (hv : ¬ S v) :
    ¬ S u ∧ Relation.TransGen R' u v := by
  induction hp with
  | single h => exact ⟨hback _ _ h hv, hf _ _ (hback _ _ h hv) hv h⟩
  | tail _ h ih =>
    have hm := hback _ _ h hv
    obtain ⟨hu, hp⟩ := ih hm
    exact ⟨hu, hp.trans (hf _ _ hm hv h)⟩

/-- A path starting inside the closed set remains there with increasing rank. -/
theorem closed_path_direct {R : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop}
    {rank : AsyncCopy.Ref × Bool → Nat}
    (hc : ∀ u v, R u v → S u → S v ∧ rank u < rank v)
    {u v : AsyncCopy.Ref × Bool} (hp : Relation.TransGen R u v) (hu : S u) :
    S v ∧ rank u < rank v := by
  induction hp with
  | single h => exact hc _ _ h hu
  | tail _ h ih =>
    obtain ⟨hm, hleft⟩ := ih
    obtain ⟨hv, hright⟩ := hc _ _ h hm
    exact ⟨hv, hleft.trans hright⟩

/-- Transfer cycle freedom when new nodes are closed in the particular order being checked. -/
theorem acyclic_direct {R R' : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop}
    {rank : AsyncCopy.Ref × Bool → Nat}
    (hc : ∀ u v, R u v → S u → S v ∧ rank u < rank v)
    (hf : ∀ u v, ¬ S u → ¬ S v → R u v → Relation.TransGen R' u v)
    (hold : ∀ n, ¬ Relation.TransGen R' n n) : ∀ n, ¬ Relation.TransGen R n n := by
  classical
  intro n hp
  by_cases hn : S n
  · exact Nat.lt_irrefl _ (closed_path_direct hc hp hn).2
  · exact hold n (old_path_direct (R := R)
      (fun u v he hn' hu => hn' (hc u v he hu).1) hf hp hn).2

/-- A frame transfers the memory orders using their own relevant edges. In particular, extra
dependency witnesses do not change the closure needed for the memory orders. -/
theorem Transport.orderOk_of_orders (h : Transport L K A X Y S) (hX : OrderOk L K A X)
    (rank : AsyncCopy.Ref × Bool → Nat)
    (hc : ∀ u v, stageCausality L Y u v → S u → S v ∧ rank u < rank v)
    (hobs : ∀ x w, SyncObserved L Y x w → S (x, false) →
      S (w, true) ∧ rank (x, false) < rank (w, true))
    (hobj : ∀ o u v, SyncObjectOrder L Y o u v → S u → S v ∧ rank u < rank v)
    (hasync : ∀ m i p y, MBarrier.Before (Y.objects m) (.async i p) y →
      ¬ S (.thread i, false) ∧ ¬ S (.async i p, true))
    (hdep : ∀ o, o.Enabling → ∀ n,
      ¬ Relation.TransGen (fun a c => DepStep L K Y a c ∨ ObjectOrder L Y o a c) n n) :
    OrderOk L K A Y := by
  have hb : ∀ u v, stageCausality L Y u v → ¬ S v → ¬ S u :=
    fun _ _ he hn hp => hn (hc _ _ he hp).1
  refine ⟨?_, ?_, ?_, hdep, h.initFence⟩
  · intro x w ho hp
    classical
    by_cases hs : S (x, false)
    · obtain ⟨hw, hr⟩ := hobs x w ho hs
      exact Nat.lt_irrefl _ (hr.trans (closed_path_direct hc hp hw).2)
    · obtain ⟨hw, hp⟩ := old_path_direct hb h.cause hp hs
      exact hX.observation x w (h.observed x w hs hw ho) hp
  · intro o
    apply acyclic_direct (S := S) (rank := rank) _ _ (hX.object o)
    · rintro u v (he | he)
      · exact hc u v he
      · exact hobj o u v he
    · intro u v hu hv he
      rcases he with he | he
      · exact Relation.TransGen.mono (fun _ _ => Or.inl) _ _ (h.cause u v hu hv he)
      · exact .single (.inr (h.objectSync o u v hu hv he))
  · intro m i p y hb'
    obtain ⟨hi, hq⟩ := hasync m i p y hb'
    refine ⟨h.asyncSelf m i p y hb', fun hs hp => ?_⟩
    obtain ⟨hy, hp⟩ := old_path_direct hb h.cause hp hi
    obtain ⟨-, -, ho⟩ := h.object (.mbar m) _ _ hq hy ⟨rfl, rfl, hb'⟩
    exact (hX.asyncObject m i p y ho).2 (h.asyncObserved m i p y hq hy hs) hp

end SinkFrame

end PTX
