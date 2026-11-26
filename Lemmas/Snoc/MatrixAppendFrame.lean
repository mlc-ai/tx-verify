-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpLanes
public import Lemmas.Snoc.SnocExit

@[expose] public section

/-! # Appending warp-level matrix events to their lanes: the execution-order axioms

A proof tool for the warp-level matrix instructions (`ldmatrix`, `stmatrix`, `movmatrix`,
`mma.sync`). A matrix event of one lane (kind `.matrix op own recv`, `Kind.MatrixColl`) is ready
only together with the matrix events of the same per-thread ordinal of the 32 lanes of its warp
(DEP-ORDER, DEP-WARP-MATRIX), so a progress step appends one matrix event to each lane at once
(`Execution.appendLanes`). This file is the copy, for the matrix kind, of the lemmas that
`Lemmas/Step/WarpAcyclic.lean` proves for the lane collectives (`Kind.LaneColl`: shuffles,
elections, warp barriers and ballots), which do not cover matrix events:

* the return of a thread's last matrix event has no outgoing waiting dependency
  (`matrix_return_sink_of_effects`, the copy of `quiet_return_sink_of_effects`);
* the appended matrix events change no memory access, no asynchronous stage and no barrier,
  register or Tensor Core rendezvous (`appendLanes_memReads_matrix` and its neighbours);
* a new matrix event fills a need of an old event only as a matrix event of the same warp and
  ordinal (`MatrixMatch`, `appendLanes_witness_new_matrix`);
* when no new event matches an old one, every new waiting dependency enters a new event
  (`appendLanes_waits_cases_matrix`), so the new events form a sink frame of the extension
  (`appendLanes_sinkFrame_matrix`) and the execution-order axioms transfer. -/

namespace PTX
open AsyncCopy
noncomputable section

/-- The kinds of the warp-level matrix events: the completed `ldmatrix`, `stmatrix`, `movmatrix`
or `mma.sync` of one lane (DEP-WARP-MATRIX). -/
def Kind.MatrixColl : Kind → Prop
  | .matrix .. => True
  | _ => False

namespace Kind.MatrixColl
variable {k : Kind}

/-- A matrix kind differs from every kind that is none. -/
theorem ne {k' : Kind} (hw : k.MatrixColl) (hk : ¬ k'.MatrixColl) : k ≠ k' :=
  fun h => hk (h ▸ hw)

/-- A matrix event issues and awaits no asynchronous operation. -/
theorem asyncSilent (hw : k.MatrixColl) : k.AsyncSilent := by
  cases k <;> simp_all [Kind.MatrixColl, Kind.AsyncSilent]

/-- A matrix event counts towards the size of an execution. -/
theorem counts {e : Event} (hw : e.kind.MatrixColl) : e.counts = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> first | exact (hw : False).elim | rfl

/-- An event of a matrix kind is a matrix event of Core (`isMatrix`). -/
theorem isMatrix_eq {e : Event} (hw : e.kind.MatrixColl) : PTX.isMatrix e = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> first | exact (hw : False).elim | rfl

/-- A matrix event reads no memory: a matrix load reads its row by an ordinary read before it. -/
theorem readsMem (hw : k.MatrixColl) : k.readsMem = false := by
  cases k <;> first | exact (hw : False).elim | rfl

/-- A matrix event is no ballot, mode vote, reduction, match or `activemask`. -/
theorem laneValue (hw : k.MatrixColl) : k.laneValue = false := by
  cases k <;> first | exact (hw : False).elim | rfl

/-- A matrix event is of no class of masked warp collectives. -/
theorem class_none {Q V : Type} {c : Kind → Option (WarpPart Q V)}
    (hc : ∀ op own recv, c (.matrix op own recv) = none) (hw : k.MatrixColl) : c k = none := by
  cases k <;> first | exact (hw : False).elim | exact hc _ _ _

end Kind.MatrixColl

/-- A Core matrix event has a matrix kind. -/
theorem Kind.MatrixColl.of_isMatrix {e : Event} (h : isMatrix e = true) : e.kind.MatrixColl := by
  obtain ⟨pc, k⟩ := e
  cases k <;> trivial

/-! ### The return of a thread's last matrix event is a waiting-graph sink -/

section
variable {L : Launch} {X : Execution} {f : EvId} {pc : Nat} {k : Kind}

private theorem matrix_other_kind (hi : X.get f = some ⟨pc, k⟩) (hk : k.MatrixColl) {pc' : Nat}
    {k' : Kind} (h : X.get f = some ⟨pc', k'⟩) (hk' : ¬ k'.MatrixColl) : False := by
  rw [hi] at h
  cases h
  exact hk' hk

private theorem matrix_no_object_before (ht : TmaOk X) (hi : X.get f = some ⟨pc, k⟩)
    (hk : k.MatrixColl) (m : Loc) (target : Ref) :
    ¬ MBarrier.Before (X.objects m) (.thread f) target := by
  rintro ⟨a, b, ra, rb, ha, hid, _⟩
  obtain ⟨ho, -⟩ := ((ht.2.2.1 m).2.1 ra (List.mem_of_getElem? ha))
  have hnone : objectAction X X.async m (.thread f) = none := by
    simp only [objectAction, hi]
    cases k <;> first | exact (hk : False).elim | rfl
  rw [hid, hnone] at ho
  cases ho

private theorem matrix_no_cluster (hcl : ClusterHistoryOk L X) (hi : X.get f = some ⟨pc, k⟩)
    (hk : k.MatrixColl) {j : EvId} {b : Bool} : ¬ ClusterWaits L X f j true b := by
  have noRecord {c : Nat} {record : ClusterBarrier.Record EvId}
      (hr : record ∈ X.clusters c) (he : f ∈ record.refs) : False := by
    rcases hcl.ref_operation hr he with ⟨pc, op, hp⟩ | ⟨pc, hp⟩
    all_goals exact matrix_other_kind hi hk hp id
  rintro ⟨_, _, hh⟩
  rcases hh with ⟨c, i, j, record, q, hr, hq, hij, he, hf, _⟩ |
    ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩
  · exact noRecord (List.mem_of_getElem? hr) he
  all_goals cases hb

private theorem matrix_no_memWrites (hi : X.get f = some ⟨pc, k⟩) (hk : k.MatrixColl)
    (a : Acc) (bs : List Byte) : ¬ X.MemWrites (.thread f) a bs := by
  rintro (⟨pc', hp⟩ | ⟨old, pc', hp⟩)
  all_goals exact matrix_other_kind hi hk hp id

private theorem matrix_no_threadFence (hi : X.get f = some ⟨pc, k⟩) (hk : k.MatrixColl)
    (sem : FenceSem) (s : MbarScope) : ¬ X.ThreadFence f sem s := by
  rintro ⟨pc', hp⟩
  exact matrix_other_kind hi hk hp id

/-- **The return of a thread's last matrix event has no outgoing waiting dependency** (the copy of
`quiet_return_sink_of_effects` for the matrix kind): a matrix event has no asynchronous effect, no
mbarrier-object action, no cluster-barrier record, no memory write and no fence. -/
theorem matrix_return_sink_of_effects (hv : EffectValidity L X) (hcl : ClusterHistoryOk L X)
    (hi : X.get f = some ⟨pc, k⟩) (hk : k.MatrixColl) (hlast : f.2 + 1 = (X.tr f.1).length)
    (hord : ∀ cta j, ¬ Tmem.Pair.Precedes L X cta f j) :
    ∀ v, ¬ Waits L X (.thread f, true) v := by
  intro v
  rintro (⟨_, hb, _, _⟩ | ⟨_, _, i, j, hi', _, hij, hs, hl⟩ | ⟨i, j, hi', _, hb⟩ |
    ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨_, _, hso⟩ | ⟨_, _, m, hb⟩ | ⟨i, j, hi', _, hw⟩ |
    ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨_, _, i, j, hi', _, hsc⟩ | ⟨i, j, hi', _, hr⟩ |
    ⟨_, _, i, j, hi', _, cta, hp⟩ | ⟨_, _, i, j, hi', _, hfs⟩ | ⟨_, _, his⟩)
  · cases hb
  · cases hi'
    rw [← hij] at hl
    omega
  · rcases hb.2.2 with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩ <;> cases hb
  · cases hb
  · cases hb
  · rcases hso with ⟨_, hb, _, _⟩ | ⟨_, _, hedge⟩
    · cases hb
    · exact hedge
  · exact matrix_no_object_before hv.tma hi hk m _ hb
  · cases hi'
    exact matrix_no_cluster hcl hi hk hw
  · cases hb
  · cases hb
  · cases hi'
    obtain ⟨a, b, bs, cs, hw, -, -, -, -, -, -, -, -, -⟩ := hsc
    exact matrix_no_memWrites hi hk a bs hw
  · cases hr.1
  · cases hi'
    exact hord cta j hp
  · cases hi'
    rcases hfs with ⟨w, r, a, b, bs, cs, se, sf, hw, -, -, hhead, -⟩ | ⟨⟨s, s', hsc, -, -⟩, -⟩
    · rcases hhead with ⟨rfl, -, -⟩ | ⟨sem, hf, -, -, -⟩
      · exact matrix_no_memWrites hi hk a bs hw
      · exact matrix_no_threadFence hi hk sem se hf
    · exact matrix_no_threadFence hi hk .sc s hsc
  · obtain ⟨hb, _, _⟩ := his
    cases hb

end
end
end PTX

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

/-- A new matrix event `i` and an old matrix event `j` of one instance (DEP-WARP-MATRIX): `i` is
an event of a lane of `j`'s warp, and both are the matrix events of one ordinal of their threads.
This is the only way a new matrix event can fill a need of an old event
(`appendLanes_witness_new_matrix`). -/
def MatrixMatch (L : Launch) (Y : Execution) (i j : EvId) : Prop :=
  (∃ l < 32, i.1 = warpLane L j.1 l) ∧ ∃ n, Y.MatrixK i n ∧ Y.MatrixK j n

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {ds : List Nat} {ev : Nat → Event}

local notation "Y" => Execution.appendLanes X ds ev

private theorem not_matrix {k : Kind} (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    (hk : ¬ k.MatrixColl) : ∀ h ∈ ds, (ev h).kind ≠ k := fun h hh => (hw h hh).ne hk

/-- An event of the extension whose kind is no matrix kind is an event of `X`. -/
theorem appendLanes_old_of_not_matrix (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {i : EvId}
    {pc : Nat} {k : Kind} (hk : ¬ k.MatrixColl) (h : (Y).get i = some ⟨pc, k⟩) :
    i.2 < (X.tr i.1).length ∧ X.get i = some ⟨pc, k⟩ := by
  have hx := (appendLanes_get_kind (not_matrix hw hk)).mp h
  exact ⟨len_of_get hx, hx⟩

/-- The matrix events of an old position are those of `X`, with the same ordinal. -/
theorem appendLanes_matrixK_old {v : EvId} {n : Nat} (hv : v.2 < (X.tr v.1).length) :
    (Y).MatrixK v n ↔ X.MatrixK v n := by
  simp only [Execution.MatrixK, appendLanes_get_old hv, appendLanes_take hv.le]

/-- The ordinal of a new matrix event is the number of matrix events of its thread in `X`. -/
theorem appendLanes_matrixK_new (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {h n : Nat}
    (hh : h ∈ ds) : (Y).MatrixK (h, (X.tr h).length) n ↔ n = (X.tr h).countP isMatrix := by
  have hk : ((Y).tr h).take (X.tr h).length = X.tr h := by
    rw [appendLanes_take (i := (h, (X.tr h).length)) le_rfl, List.take_length]
  constructor
  · rintro ⟨-, hc⟩
    simp only at hc
    rw [hk] at hc
    exact hc.symm
  · rintro rfl
    exact ⟨⟨_, appendLanes_get_new hh, (hw h hh).isMatrix_eq⟩, by simp only; rw [hk]⟩

/-- The appended matrix events are no warp-collective `tcgen05` events. -/
theorem appendLanes_tcK_matrix (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {v : EvId} {k : Nat} :
    (Y).TcK v k ↔ X.TcK v k := by
  have hev : (∃ q, (Y).get v = some q ∧ isTcColl q = true) ↔
      (∃ q, X.get v = some q ∧ isTcColl q = true) := by
    constructor
    · rintro ⟨q, hq, hc⟩
      rcases appendLanes_get_cases hq with ⟨-, hq⟩ | ⟨hh, -, rfl⟩
      · exact ⟨q, hq, hc⟩
      · obtain ⟨pc, kd, he⟩ := isTcColl_tc hc
        exact ((hw _ hh).ne id (congrArg Event.kind he)).elim
    · rintro ⟨q, hq, hc⟩
      exact ⟨q, by rw [appendLanes_get_old (len_of_get hq), hq], hc⟩
  constructor
  · rintro ⟨hq, hn⟩
    obtain ⟨q, hq', hc⟩ := hev.mp hq
    refine ⟨⟨q, hq', hc⟩, ?_⟩
    rwa [appendLanes_take (len_of_get hq').le] at hn
  · rintro ⟨hq, hn⟩
    obtain ⟨q, hq', hc⟩ := hq
    refine ⟨hev.mpr ⟨q, hq', hc⟩, ?_⟩
    rwa [appendLanes_take (len_of_get hq').le]

/-- The appended matrix events are no `bar.sync`. -/
theorem appendLanes_ctaBarK_matrix (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {v : EvId}
    {key : Nat} : CtaBarK L Y v key ↔ CtaBarK L X v key := by
  simp only [CtaBarK, Execution.IsBarrier,
    appendLanes_get_kind (not_matrix hw (k := .bar _ _) id)]
  rfl

/-- The appended matrix events are no named-barrier arrivals. -/
theorem appendLanes_ctaBarArrivalK_matrix (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {v : EvId}
    {key : Nat} : CtaBarArrivalK L Y v key ↔ CtaBarArrivalK L X v key := by
  have h (pc b : Nat) (c : Option Nat) (m : BarMode) :
      (Y).get v = some ⟨pc, .bar b c m⟩ ↔ X.get v = some ⟨pc, .bar b c m⟩ :=
    appendLanes_get_kind (not_matrix hw (k := .bar _ _ _) id)
  simp only [CtaBarArrivalK, Execution.IsBarArrival, h]
  rfl

/-- The appended matrix events add no asynchronous stage. -/
theorem appendLanes_asyncPresent_matrix (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    {i : EvId} {p : Part} : (Y).AsyncPresent i p ↔ X.AsyncPresent i p :=
  appendLanes_transport (fun Z => Z.AsyncPresent i p) hd
    (fun _ h hh => (hw h hh).asyncSilent.snoc_asyncPresent)

/-- The appended matrix events read no memory. -/
theorem appendLanes_memReads_matrix (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    {v : Ref} {a : Acc} {bs : List (Option Byte)} : (Y).MemReads v a bs ↔ X.MemReads v a bs :=
  appendLanes_transport (fun Z => Z.MemReads v a bs) hd
    (fun _ h hh => (hw h hh).asyncSilent.snoc_memReads (fun _ _ => (hw h hh).ne id)
      (fun _ _ _ => (hw h hh).ne id))

/-- The appended matrix events write no memory. -/
theorem appendLanes_memWrites_matrix (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    {v : Ref} {a : Acc} {bs : List Byte} : (Y).MemWrites v a bs ↔ X.MemWrites v a bs :=
  appendLanes_transport (fun Z => Z.MemWrites v a bs) hd
    (fun _ h hh => (hw h hh).asyncSilent.snoc_memWrites (fun _ _ => (hw h hh).ne id)
      (fun _ _ _ => (hw h hh).ne id))

/-- The appended matrix events are no register requests. -/
theorem appendLanes_request_matrix (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {i : EvId}
    {pc : Nat} {inc : Bool} {n inst : Nat} : SetMaxNReg.Request Y i pc inc n inst ↔
      SetMaxNReg.Request X i pc inc n inst :=
  appendLanes_get_kind (not_matrix hw id)

/-- The register requests of one warp instance are those of `X`. -/
theorem appendLanes_sameRequest_matrix (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {i j : EvId} :
    SetMaxNReg.SameRequest L Y i j ↔ SetMaxNReg.SameRequest L X i j := by
  have hord {f : EvId} {pc : Nat} {inc : Bool} {n inst : Nat}
      (hf : SetMaxNReg.Request X f pc inc n inst) : SetMaxNReg.ordinal Y f =
        SetMaxNReg.ordinal X f := by
    unfold SetMaxNReg.ordinal
    rw [appendLanes_take (len_of_get hf).le]
  constructor
  · rintro ⟨hs, ho, pc, inc, n, ei, fi, hi, hj⟩
    have hi' := (appendLanes_request_matrix hw).mp hi
    have hj' := (appendLanes_request_matrix hw).mp hj
    rw [hord hi', hord hj'] at ho
    exact ⟨hs, ho, pc, inc, n, ei, fi, hi', hj'⟩
  · rintro ⟨hs, ho, pc, inc, n, ei, fi, hi, hj⟩
    rw [← hord hi, ← hord hj] at ho
    exact ⟨hs, ho, pc, inc, n, ei, fi, (appendLanes_request_matrix hw).mpr hi,
      (appendLanes_request_matrix hw).mpr hj⟩

/-- The register rendezvous edges are those of `X`. -/
theorem appendLanes_regWaits_matrix (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {i j : EvId}
    {b b' : Bool} : SetMaxNReg.WaitEdge L Y i j b b' ↔ SetMaxNReg.WaitEdge L X i j b b' := by
  simp only [SetMaxNReg.WaitEdge, appendLanes_sameRequest_matrix hw]

/-- A release/acquire synchronization of the extension is one of `X`. -/
theorem appendLanes_synchronizesWith_matrix (hd : ds.Nodup)
    (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {i j : EvId} (h : synchronizesWith L Y i j) :
    synchronizesWith L X i j := by
  obtain ⟨a, b, bs, cs, hwr, hrd, hr, ha, hl, hn, hz, hs, ht, hf⟩ := h
  have hrd' := (appendLanes_memReads_matrix hd hw).mp hrd
  refine ⟨a, b, bs, cs, (appendLanes_memWrites_matrix hd hw).mp hwr, hrd', hr, ha, hl, hn, hz,
    hs, ht, fun k hk => ?_⟩
  rw [← le_appendLanes.2.1 (.thread j) k ⟨b, cs, hrd'⟩]
  exact hf k hk

/-- A fence synchronization of the extension is one of `X`. -/
theorem appendLanes_fenceSync_matrix (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    {i j : EvId} (h : FenceSync L Y i j) : FenceSync L X i j := by
  have fence {v : EvId} {sem : FenceSem} {s : MbarScope} (h : (Y).ThreadFence v sem s) :
      X.ThreadFence v sem s := by
    obtain ⟨pc, hp⟩ := h
    exact ⟨pc, (appendLanes_get_kind (not_matrix hw id)).mp hp⟩
  rcases h with ⟨w, rd, aa, bb, bs, cs, se, sf, hwr, hst, hsr, hrel, hacq, hfn, hl, hn, hz, hs1,
      hs2, hs3, hs4, hf⟩ | ⟨⟨s, s', hs, hs', hm⟩, hfsc⟩
  · have hsr' : StrongRead X rd bb cs := by
      rcases hsr with ⟨⟨pc, hp⟩, hb⟩ | ⟨n, ⟨pc, hp⟩, hb⟩
      · exact .inl ⟨⟨pc, (appendLanes_get_kind (not_matrix hw id)).mp hp⟩, hb⟩
      · exact .inr ⟨n, ⟨pc, (appendLanes_get_kind (not_matrix hw id)).mp hp⟩, hb⟩
    refine .inl ⟨w, rd, aa, bb, bs, cs, se, sf, (appendLanes_memWrites_matrix hd hw).mp hwr,
      hst, hsr', ?_, ?_, ?_, hl, hn, hz, hs1, hs2, hs3, hs4, fun k hk => ?_⟩
    · rcases hrel with h | ⟨sem, h, h1⟩
      · exact .inl h
      · exact .inr ⟨sem, fence h, h1⟩
    · rcases hacq with h | ⟨sem, h, h1⟩
      · exact .inl h
      · exact .inr ⟨sem, fence h, h1⟩
    · obtain ⟨sem, s, h | h⟩ := hfn
      · exact ⟨sem, s, .inl (fence h)⟩
      · exact ⟨sem, s, .inr (fence h)⟩
    · rw [← le_appendLanes.2.1 (.thread rd) k ⟨bb, cs, hsr'.memReads⟩]
      exact hf k hk
  · exact .inr ⟨⟨s, s', fence hs, fence hs', hm⟩, hfsc⟩

/-- **A new matrix event fills a need of an old event only as a matrix event of the same warp
and ordinal** (`MatrixMatch`): every other need is filled by an event of another kind, by an exit,
by a recorded barrier, cluster or allocator participant, by an object record or by an asynchronous
stage, and the histories of `X`, which the append keeps, name only old events. -/
theorem appendLanes_witness_new_matrix (hX : Consistent L K A mem0 X)
    (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {x j : EvId}
    (hx : x.1 ∈ ds ∧ x.2 = (X.tr x.1).length) (h : Witness L Y (.thread x) j) :
    MatrixMatch L Y x j := by
  obtain ⟨fills, hmem, -, hf⟩ := h
  have hnone : X.get x = none :=
    (appendLanes_threadAppend (X := X) (ds := ds) (ev := ev)).fresh x hx
  have notX : ∀ {q}, X.get x = some q → False := fun h => by rw [hnone] at h; cases h
  have hgx : (Y).get x = some (ev x.1) := by
    obtain ⟨x1, x2⟩ := x
    obtain ⟨h1, h2⟩ := hx
    simp only at h1 h2
    subst h2
    exact appendLanes_get_new h1
  have hlc := hw x.1 hx.1
  have kindNew : ∀ {pc k}, (Y).get x = some ⟨pc, k⟩ → (ev x.1).kind = k := fun h => by
    rw [hgx] at h; rw [Option.some.inj h]
  have notK : ∀ {pc k}, (Y).get x = some ⟨pc, k⟩ → ¬ k.MatrixColl → False :=
    fun h hk => hk (kindNew h ▸ hlc)
  have mapped : ∀ {α : Type} (l : List α) (P : α → Ref → Prop),
      Need.node fills ∈ l.map (fun a => Need.node (P a)) → ∃ a ∈ l, fills = P a := by
    intro α l P hm
    obtain ⟨a, ha', he⟩ := List.mem_map.mp hm
    exact ⟨a, ha', (Need.node.inj he).symm⟩
  -- a masked collective waits for an event of its class or an exit: no matrix event
  have maskCase : ∀ {Q V : Type} (c : Kind → Option (WarpPart Q V)),
      (∀ op own recv, c (.matrix op own recv) = none) →
      Need.node fills ∈ maskNeeds L c Y j → False := by
    intro Q V c hc hm
    unfold maskNeeds at hm
    generalize ((Y).get j).bind (fun ev => c ev.kind) = o at hm
    cases o with
    | none => simp at hm
    | some p =>
      obtain ⟨l, -, rfl⟩ := mapped _ _ hm
      obtain ⟨j', he, hmw⟩ := hf
      cases he
      obtain ⟨-, m, n, q, -, ⟨-, ev', p', hg, hc', -⟩ | ⟨-, ⟨pc, hg⟩, -⟩⟩ := hmw
      · rw [hgx] at hg
        cases hg
        rw [hlc.class_none hc] at hc'
        cases hc'
      · exact (notK hg id).elim
  have tcCase : Need.node fills ∈ tcNeeds L Y j → False := by
    intro hm
    obtain ⟨l, -, rfl⟩ := mapped _ _ (by unfold tcNeeds at hm; exact hm)
    obtain ⟨j', he, ⟨q, hg, hc⟩, -⟩ := hf
    cases he
    obtain ⟨pc, kd, rfl⟩ := isTcColl_tc hc
    exact notK hg id
  unfold Needs at hmem
  cases hget : (Y).get j with
  | none => simp [hget] at hmem
  | some q =>
  simp only [hget] at hmem
  obtain ⟨pc0, kd⟩ := q
  cases kd
  case shfl => exact (maskCase shflClass (fun _ _ _ => rfl) hmem).elim
  case vote => exact (maskCase voteClass (fun _ _ _ => rfl) hmem).elim
  case voteMode => exact (maskCase voteClass (fun _ _ _ => rfl) hmem).elim
  case redux => exact (maskCase reduxClass (fun _ _ _ => rfl) hmem).elim
  case match_ => exact (maskCase matchClass (fun _ _ _ => rfl) hmem).elim
  case elect mask inst leader =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', pc', ld, he, hg⟩ := hf
    cases he
    exact (notK hg id).elim
  case warpBar mask inst =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, pc', hg⟩ := hf
    cases he
    exact (notK hg id).elim
  case matrix op own recv =>
    obtain ⟨l, hl, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, hk | ⟨⟨pc', hg⟩, -⟩⟩ := hf
    · cases he
      exact ⟨⟨l, List.mem_range.mp hl, rfl⟩, _, hk, ⟨_, hget, rfl⟩, rfl⟩
    · cases he
      exact (notK hg id).elim
  case setMaxReg inc n inst =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, -, -, pc', inc', n', ei, fi, -, hg⟩ := hf
    cases he
    exact (notK hg id).elim
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
      obtain ⟨q', hq'⟩ := hp
      exact (notX hq').elim
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
        exact (notK hwrite id).elim
    all_goals simp [KindNeeds] at hmem
  all_goals simp [KindNeeds] at hmem


/-- **Every new dependency enters a new event**, when no new matrix event matches an old one. -/
theorem appendLanes_waits_cases_matrix (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    (hfresh : ∀ h ∈ ds, ∀ j : EvId, j.2 < (X.tr j.1).length →
      ¬ MatrixMatch L Y (h, (X.tr h).length) j)
    {u v : Ref × Bool} (h : Waits L Y u v) : AppendedNode X ds v ∨ Waits L X u v := by
  have le : X.le Y := le_appendLanes
  have ha := appendLanes_threadAppend (X := X) (ds := ds) (ev := ev)
  have hpres : ∀ i p, (Y).AsyncPresent i p → X.AsyncPresent i p :=
    fun _ _ => (appendLanes_asyncPresent_matrix hd hw).mp
  have newj {j : EvId} (hj : j.1 ∈ ds ∧ j.2 = (X.tr j.1).length) {b : Bool} :
      AppendedNode X ds (.thread j, b) :=
    ⟨j.1, hj.1, congrArg Ref.thread (Prod.ext rfl hj.2)⟩
  -- a match of a new matrix event with an old one is excluded by freshness
  have nofresh {i j : EvId} (hi : i.1 ∈ ds ∧ i.2 = (X.tr i.1).length)
      (hj : j.2 < (X.tr j.1).length) (hm : MatrixMatch L Y i j) : False := by
    obtain ⟨i1, i2⟩ := i
    obtain ⟨hh, h2⟩ := hi
    simp only at hh h2
    rw [h2] at hm
    exact hfresh i1 hh j hj hm
  have getOld {i : EvId} {q : Event} (hq : (Y).get i = some q) :
      (i.2 < (X.tr i.1).length ∧ X.get i = some q) ∨ (i.1 ∈ ds ∧ i.2 = (X.tr i.1).length) := by
    rcases appendLanes_get_cases hq with h | ⟨h1, h2, -⟩
    · exact .inl h
    · exact .inr ⟨h1, h2⟩
  obtain ⟨u, b⟩ := u
  obtain ⟨v, b'⟩ := v
  rcases h with ⟨h1, h2, h3, hp⟩ | ⟨h1, h2, i, j, hi, hj, hthread, hs, hl⟩ |
    ⟨i, j, hi, hj, hbar⟩ | ⟨h1, h2, i, j, hi, hj, hwarp, k, his, hjs⟩ |
    ⟨h1, h2, i, j, hi, hj, hwarp, k, hit, hjt⟩ | ⟨h1, h2, hso⟩ | ⟨h1, h2, m, ho⟩ |
    ⟨i, j, hi, hj, hcl⟩ | ⟨h1, h2, j, hj, hwit⟩ | ⟨h1, h2, i, j, hi, hj, hwb⟩ |
    ⟨h1, h2, i, j, hi, hj, hms⟩ | ⟨i, j, hi, hj, hrw⟩ | ⟨h1, h2, i, j, hi, hj, cta, hpre⟩ |
    ⟨h1, h2, i, j, hi, hj, hfs⟩ | ⟨h1, h2, his⟩
  · subst h1
    cases u with
    | thread i =>
      obtain ⟨q, hq⟩ := hp
      rcases getOld hq with ⟨-, hq⟩ | hn
      · exact .inr (.inl ⟨rfl, h2, h3, q, hq⟩)
      · exact .inl (newj hn)
    | «async» i p => exact .inr (.inl ⟨rfl, h2, h3, hpres i p hp⟩)
  · subst hi hj
    rcases appendLanes_index_cases hl with hold | hn
    · exact .inr (.inr (.inl ⟨h1, h2, i, j, rfl, rfl, hthread, hs, hold⟩))
    · exact .inl (newj hn)
  · exact .inr (.inr (.inr (.inl ⟨i, j, hi, hj, (Proof.ExtensionWait.ctaBarWaits_iff hX le rfl
      (fun _ _ => appendLanes_ctaBarK_matrix hw)
      (fun _ _ => appendLanes_ctaBarArrivalK_matrix hw) i j b b').mp hbar⟩)))
  · -- a shuffle rendezvous joins two shuffles, which are old events
    subst hi hj
    have old {x : EvId} (hx : (Y).ShflK x k) : x.2 < (X.tr x.1).length := by
      obtain ⟨⟨pc, m, a, b, c, r, o, hs⟩, -⟩ := hx
      exact (appendLanes_old_of_not_matrix hw id hs).1
    exact .inr (.inr (.inr (.inr (.inl ⟨h1, h2, i, j, rfl, rfl, hwarp, k,
      (appendLanes_shflK_old (old his)).mp his, (appendLanes_shflK_old (old hjs)).mp hjs⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨h1, h2, i, j, hi, hj, hwarp, k,
      (appendLanes_tcK_matrix hw).mp hit, (appendLanes_tcK_matrix hw).mp hjt⟩)))))
  · subst h1 h2
    rcases hso with ⟨-, h, -⟩ | ⟨-, -, hse⟩
    · cases h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl,
      .inr ⟨rfl, rfl, ha.stageEdge hX hpres hse⟩⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, h2, m, ho⟩)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, j, hi, hj,
      (Proof.ExtensionWait.clusterWaits_iff hX le rfl i j b b').mp hcl⟩))))))))
  · subst hj
    by_cases hjn : j.1 ∈ ds ∧ j.2 = (X.tr j.1).length
    · exact .inl (newj hjn)
    have hjo : j.2 < (X.tr j.1).length := by
      obtain ⟨fills, hm, -⟩ := hwit
      unfold Needs at hm
      cases hq : (Y).get j with
      | none => simp [hq] at hm
      | some q =>
        rcases getOld hq with ⟨h, -⟩ | h
        · exact h
        · exact (hjn h).elim
    by_cases hun : ∃ x, x.1 ∈ ds ∧ x.2 = (X.tr x.1).length ∧ u = .thread x
    · obtain ⟨x, hx1, hx2, rfl⟩ := hun
      exact (nofresh ⟨hx1, hx2⟩ hjo
        (appendLanes_witness_new_matrix hX hw ⟨hx1, hx2⟩ hwit)).elim
    · refine .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, h2, j, rfl,
        ha.witness hpres ?_ hjn hwit⟩)))))))))
      rintro ⟨x, hx, rfl⟩
      exact hun ⟨x, hx.1, hx.2, rfl⟩
  · -- a warp-barrier edge joins two warp barriers, which are old events
    subst hi hj
    obtain ⟨hs, mask, inst, ⟨pc, hei⟩, ⟨pc', hej⟩⟩ := hwb
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, h2,
      i, j, rfl, rfl, hs, mask, inst, ⟨pc, (appendLanes_old_of_not_matrix hw id hei).2⟩,
      ⟨pc', (appendLanes_old_of_not_matrix hw id hej).2⟩⟩))))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1, h2, i, j, hi, hj, appendLanes_synchronizesWith_matrix hd hw hms⟩)))))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨i, j, hi, hj, (appendLanes_regWaits_matrix hw).mp hrw⟩))))))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1, h2, i, j, hi, hj, cta, hpre⟩)))))))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inl ⟨h1, h2, i, j, hi, hj, appendLanes_fenceSync_matrix hd hw hfs⟩))))))))))))))
  · obtain ⟨-, -, i, p, rfl, rfl, ⟨q, hq⟩, hap, hm⟩ := his
    have hapX := hpres i p hap
    have hio : i.2 < (X.tr i.1).length :=
      refPresent_issuer_lt hX.effectValidity (f := .async i p) hapX
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inr ⟨h1, h2, h1, h2, i, p, rfl, rfl, ⟨q, by rwa [appendLanes_get_old hio] at hq⟩, hapX,
        hm⟩))))))))))))))

/-- A new arrival waits only for returns. -/
private theorem arrival_to_return_matrix (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    {h : Nat} {v : Ref} {b' : Bool}
    (hwt : Waits L Y (.thread (h, (X.tr h).length), false) (v, b')) : b' = true := by
  have le : X.le Y := le_appendLanes
  have noOld : ¬ Waits L X (.thread (h, (X.tr h).length), false) (v, b') := by
    intro hx
    obtain ⟨q, hq⟩ := (waits_present hX.effectValidity hx).1
    have := len_of_get hq
    simp at this
  rcases hwt with ⟨-, -, h3, -⟩ | ⟨h1, -⟩ | ⟨i, j, hi, hj, hbar⟩ | ⟨-, h2, -⟩ | ⟨-, h2, -⟩ |
    ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨i, j, hi, hj, hcl⟩ | ⟨-, h2, -⟩ | ⟨-, h2, -⟩ |
    ⟨h1, -⟩ | ⟨i, j, hi, hj, hrw⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, his⟩
  all_goals try (first | exact h3 | exact h2 | cases h1)
  · exact (noOld (.inr (.inr (.inl ⟨i, j, hi, hj, (Proof.ExtensionWait.ctaBarWaits_iff hX le rfl
      (fun _ _ => appendLanes_ctaBarK_matrix hw)
      (fun _ _ => appendLanes_ctaBarArrivalK_matrix hw) i j _ _).mp hbar⟩)))).elim
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, j, hi, hj,
      (Proof.ExtensionWait.clusterWaits_iff hX le rfl i j _ _).mp hcl⟩))))))))).elim
  · exact hrw.2.1
  · exfalso
    obtain ⟨-, -, i, p, he, rfl, -, hap, -⟩ := his
    cases he
    have : (X.tr h).length < (X.tr h).length :=
      refPresent_issuer_lt hX.effectValidity (f := .async (h, (X.tr h).length) p)
        ((appendLanes_asyncPresent_matrix hd hw).mp hap)
    exact Nat.lt_irrefl _ this

/-- **Appending matrix events that match no old event is a sink frame** for the new events,
given that causality into old events is old: the execution-order axioms of `X` transfer to the
extension (`SinkFrame.orderOk`). -/
theorem appendLanes_sinkFrame_matrix (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    (hfresh : ∀ h ∈ ds, ∀ j : EvId, j.2 < (X.tr j.1).length →
      ¬ MatrixMatch L Y (h, (X.tr h).length) j)
    (hv : EffectValidity L Y) (hcl : ClusterHistoryOk L Y)
    (hhb : ∀ i j, j.2 < (X.tr j.1).length → baseCausality L Y i j → baseCausality L X i j) :
    SinkFrame L K A X Y (AppendedNode X ds) := by
  refine appendLanes_threadAppend.sinkFrame hX (fun i b hi => ⟨i.1, hi.1, by rw [← hi.2]⟩)
    (fun i ⟨h, hh, he⟩ => by cases he; exact ⟨hh, rfl⟩)
    (fun _ _ => (appendLanes_asyncPresent_matrix hd hw).mp) hhb
    ⟨fun n => if n.2 then 1 else 0, ?_⟩
  intro u v hwt hu
  obtain ⟨h, hh, hu1⟩ := hu
  obtain ⟨u, b⟩ := u
  simp only at hu1
  subst hu1
  cases b with
  | true =>
    exfalso
    have hget : (Y).get (h, (X.tr h).length) = some ⟨(ev h).pc, (ev h).kind⟩ :=
      appendLanes_get_new hh
    have hlast : (h, (X.tr h).length).2 + 1 = ((Y).tr (h, (X.tr h).length).1).length := by
      simp only [appendLanes_len, ite_eq_left hh]
    refine matrix_return_sink_of_effects hv hcl hget (hw h hh) hlast
      (fun cta j hc => ?_) v hwt
    obtain ⟨pc, grp, dst, act, hold⟩ := Tmem.Pair.Precedes.actual hX.tmemPair hc
    have := len_of_get hold
    simp at this
  | false =>
    have hb := arrival_to_return_matrix hX hd hw hwt
    obtain ⟨v, b'⟩ := v
    simp only at hb
    subst hb
    refine ⟨?_, by simp⟩
    rcases appendLanes_waits_cases_matrix hX hd hw hfresh hwt with hn | hx
    · exact hn
    · obtain ⟨q, hq⟩ := (waits_present hX.effectValidity hx).1
      have := len_of_get hq
      simp at this

end
end PTX.Step
