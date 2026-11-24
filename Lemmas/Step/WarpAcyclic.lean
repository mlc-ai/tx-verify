-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpAppend
public import Lemmas.Snoc.ExtensionWaitFrame
public import Lemmas.Snoc.SnocSinkFrame
public import Lemmas.Tmem.TmemPairHistory

@[expose] public section

/-! # The execution-order axioms after appending a lane collective to its lanes

A proof tool. Appending one lane-collective event (`Kind.LaneColl`: a warp collective or a
ballot) to each thread of `ds` adds waiting dependencies only into the new events, provided no
new event matches an old one (`WarpMatch`): a new event fills a need of an old event only as an
event of the same collective instance (`appendLanes_witness_new`, DEP-ORDER), and the other edges
of a new arrival go to returns of the same instance, which are new. The new returns are sinks
(`quiet_return_sink_of_effects`), so the new events form a closed terminal suffix, a sink frame of
the extension
(`appendLanes_sinkFrame_lane`). -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

/-- A new event `i` and an old event `j` of one collective instance: elections or warp barriers
with the same mask and label, shuffles of one warp with the same ordinal, or the dependency of a
ballot or mode vote `j` on the ballot `i` of a lane of its member mask (DEP-WARP-INSTANCE). These
are the only ways a new lane collective can fill a need of an old event
(`appendLanes_witness_new`) or meet it in a shuffle rendezvous. -/
def WarpMatch (L : Launch) (Y : Execution) (i j : EvId) : Prop :=
  (∃ pc pc' mask inst leader leader', Y.get i = some ⟨pc, .elect mask inst leader⟩ ∧
      Y.get j = some ⟨pc', .elect mask inst leader'⟩) ∨
    (∃ mask inst, Y.WarpBar i mask inst ∧ Y.WarpBar j mask inst) ∨
    (SameWarp L i.1 j.1 ∧ ∃ n, Y.ShflK i n ∧ Y.ShflK j n) ∨
    MaskWait L voteClass Y i j

/-- A new event of the extension, as a waiting-graph node. -/
def AppendedNode (X : Execution) (ds : List Nat) (v : Ref × Bool) : Prop :=
  ∃ h ∈ ds, v.1 = .thread (h, (X.tr h).length)

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {ds : List Nat} {ev : Nat → Event}

local notation "Y" => Execution.appendLanes X ds ev

private theorem not_lane {k : Kind} (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) (hk : ¬ k.LaneColl) :
    ∀ h ∈ ds, (ev h).kind ≠ k := fun h hh => (hw h hh).ne hk

theorem appendLanes_shflK_old {v : EvId} {n : Nat} (hv : v.2 < (X.tr v.1).length) :
    (Y).ShflK v n ↔ X.ShflK v n := by
  simp only [Execution.ShflK, appendLanes_get_old hv, appendLanes_take hv.le]

theorem appendLanes_tcK_lane (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) {v : EvId} {k : Nat} :
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

theorem appendLanes_ctaBarK_lane (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) {v : EvId} {key : Nat} :
    CtaBarK L Y v key ↔ CtaBarK L X v key := by
  simp only [CtaBarK, Execution.IsBarrier,
    appendLanes_get_kind (not_lane hw (k := .bar _ _) id)]
  rfl

theorem appendLanes_ctaBarArrivalK_lane (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) {v : EvId}
    {key : Nat} : CtaBarArrivalK L Y v key ↔ CtaBarArrivalK L X v key := by
  have h (pc b : Nat) (c : Option Nat) (m : BarMode) :
      (Y).get v = some ⟨pc, .bar b c m⟩ ↔ X.get v = some ⟨pc, .bar b c m⟩ :=
    appendLanes_get_kind (not_lane hw (k := .bar _ _ _) id)
  simp only [CtaBarArrivalK, Execution.IsBarArrival, h]
  rfl

theorem appendLanes_asyncPresent_lane (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    {i : EvId} {p : Part} : (Y).AsyncPresent i p ↔ X.AsyncPresent i p :=
  appendLanes_transport (fun Z => Z.AsyncPresent i p) hd
    (fun _ h hh => (hw h hh).asyncSilent.snoc_asyncPresent)

theorem appendLanes_memReads_lane (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    {v : Ref} {a : Acc} {bs : List (Option Byte)} : (Y).MemReads v a bs ↔ X.MemReads v a bs :=
  appendLanes_transport (fun Z => Z.MemReads v a bs) hd
    (fun _ h hh => (hw h hh).asyncSilent.snoc_memReads (fun _ _ => (hw h hh).ne id)
      (fun _ _ _ => (hw h hh).ne id))

theorem appendLanes_memWrites_lane (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    {v : Ref} {a : Acc} {bs : List Byte} : (Y).MemWrites v a bs ↔ X.MemWrites v a bs :=
  appendLanes_transport (fun Z => Z.MemWrites v a bs) hd
    (fun _ h hh => (hw h hh).asyncSilent.snoc_memWrites (fun _ _ => (hw h hh).ne id)
      (fun _ _ _ => (hw h hh).ne id))

theorem appendLanes_request_lane (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) {i : EvId} {pc : Nat}
    {inc : Bool} {n inst : Nat} : SetMaxNReg.Request Y i pc inc n inst ↔
      SetMaxNReg.Request X i pc inc n inst :=
  appendLanes_get_kind (not_lane hw id)

theorem appendLanes_sameRequest_lane (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) {i j : EvId} :
    SetMaxNReg.SameRequest L Y i j ↔ SetMaxNReg.SameRequest L X i j := by
  have hord {f : EvId} {pc : Nat} {inc : Bool} {n inst : Nat}
      (hf : SetMaxNReg.Request X f pc inc n inst) : SetMaxNReg.ordinal Y f =
        SetMaxNReg.ordinal X f := by
    unfold SetMaxNReg.ordinal
    rw [appendLanes_take (len_of_get hf).le]
  constructor
  · rintro ⟨hs, ho, pc, inc, n, ei, fi, hi, hj⟩
    have hi' := (appendLanes_request_lane hw).mp hi
    have hj' := (appendLanes_request_lane hw).mp hj
    rw [hord hi', hord hj'] at ho
    exact ⟨hs, ho, pc, inc, n, ei, fi, hi', hj'⟩
  · rintro ⟨hs, ho, pc, inc, n, ei, fi, hi, hj⟩
    rw [← hord hi, ← hord hj] at ho
    exact ⟨hs, ho, pc, inc, n, ei, fi, (appendLanes_request_lane hw).mpr hi,
      (appendLanes_request_lane hw).mpr hj⟩

theorem appendLanes_regWaits_lane (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) {i j : EvId} {b b' : Bool} :
    SetMaxNReg.WaitEdge L Y i j b b' ↔ SetMaxNReg.WaitEdge L X i j b b' := by
  simp only [SetMaxNReg.WaitEdge, appendLanes_sameRequest_lane hw]


theorem appendLanes_synchronizesWith_lane (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    {i j : EvId} (h : synchronizesWith L Y i j) : synchronizesWith L X i j := by
  obtain ⟨a, b, bs, cs, hwr, hrd, hr, ha, hl, hn, hz, hs, ht, hf⟩ := h
  have hrd' := (appendLanes_memReads_lane hd hw).mp hrd
  refine ⟨a, b, bs, cs, (appendLanes_memWrites_lane hd hw).mp hwr, hrd', hr, ha, hl, hn, hz, hs,
    ht, fun k hk => ?_⟩
  rw [← le_appendLanes.2.1 (.thread j) k ⟨b, cs, hrd'⟩]
  exact hf k hk

theorem appendLanes_fenceSync_lane (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    {i j : EvId} (h : FenceSync L Y i j) : FenceSync L X i j := by
  have fence {v : EvId} {sem : FenceSem} {s : MbarScope} (h : (Y).ThreadFence v sem s) :
      X.ThreadFence v sem s := by
    obtain ⟨pc, hp⟩ := h
    exact ⟨pc, (appendLanes_get_kind (not_lane hw id)).mp hp⟩
  rcases h with ⟨w, rd, aa, bb, bs, cs, se, sf, hwr, hst, hsr, hrel, hacq, hfn, hl, hn, hz, hs1,
      hs2, hs3, hs4, hf⟩ | ⟨⟨s, s', hs, hs', hm⟩, hfsc⟩
  · have hsr' : StrongRead X rd bb cs := by
      rcases hsr with ⟨⟨pc, hp⟩, hb⟩ | ⟨n, ⟨pc, hp⟩, hb⟩
      · exact .inl ⟨⟨pc, (appendLanes_get_kind (not_lane hw id)).mp hp⟩, hb⟩
      · exact .inr ⟨n, ⟨pc, (appendLanes_get_kind (not_lane hw id)).mp hp⟩, hb⟩
    refine .inl ⟨w, rd, aa, bb, bs, cs, se, sf, (appendLanes_memWrites_lane hd hw).mp hwr, hst,
      hsr', ?_, ?_, ?_, hl, hn, hz, hs1, hs2, hs3, hs4, fun k hk => ?_⟩
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

/-- Appending events to their lanes is a thread append. -/
theorem appendLanes_threadAppend :
    ThreadAppend X Y (fun i => i.1 ∈ ds ∧ i.2 = (X.tr i.1).length) where
  get i hi := by rw [appendLanes_get, ite_eq_right hi]
  fresh i hi := by
    obtain ⟨-, h2⟩ := hi
    unfold Execution.get; rw [h2]; exact List.getElem?_eq_none (le_refl _)
  take i hi := appendLanes_take hi.le
  tracePrefix h := le_appendLanes.1 h
  async := rfl
  tensor := rfl
  barriers := rfl
  clusters := rfl
  tmemHistory := rfl
  tmemPairing := rfl
  tmemPairBlocks := rfl
  objects _ := ⟨[], by simp; rfl, by simp⟩

/-- **A new lane collective fills a need of an old event only as an instance of the same
collective** (`WarpMatch`): every other need is filled by an event of another kind, by an exit, by a
recorded barrier, cluster or allocator participant, by an object record or by an asynchronous
stage, and the histories of `X`, which the append keeps, name only old events. -/
theorem appendLanes_witness_new (hX : Consistent L K A mem0 X)
    (hw : ∀ h ∈ ds, (ev h).kind.LaneColl) {x j : EvId} (hx : x.1 ∈ ds ∧ x.2 = (X.tr x.1).length)
    (hj : j.2 < (X.tr j.1).length) (h : Witness L Y (.thread x) j) : WarpMatch L Y x j := by
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
  have notK : ∀ {pc k}, (Y).get x = some ⟨pc, k⟩ → ¬ k.LaneColl → False :=
    fun h hk => hk (kindNew h ▸ hlc)
  have mapped : ∀ {α : Type} (l : List α) (P : α → Ref → Prop),
      Need.node fills ∈ l.map (fun a => Need.node (P a)) → ∃ a ∈ l, fills = P a := by
    intro α l P hm
    obtain ⟨a, ha', he⟩ := List.mem_map.mp hm
    exact ⟨a, ha', (Need.node.inj he).symm⟩
  have maskCase : ∀ {Q V : Type} (c : Kind → Option (WarpPart Q V)),
      Need.node fills ∈ maskNeeds L c Y j → MaskWait L c Y x j ∧ ∃ p, c (ev x.1).kind = some p := by
    intro Q V c hm
    unfold maskNeeds at hm
    generalize ((Y).get j).bind (fun ev => c ev.kind) = o at hm
    cases o with
    | none => simp at hm
    | some p =>
      obtain ⟨l, -, rfl⟩ := mapped _ _ hm
      obtain ⟨j', he, hmw⟩ := hf
      cases he
      refine ⟨hmw, ?_⟩
      obtain ⟨-, m, n, q, -, ⟨-, ev', p', hg, hc, -⟩ | ⟨-, ⟨pc, hg⟩, -⟩⟩ := hmw
      · rw [hgx] at hg
        cases hg
        exact ⟨p', hc⟩
      · exact (notK hg id).elim
  have tcCase : Need.node fills ∈ tcNeeds L Y j → False := by
    intro hm
    obtain ⟨l, -, rfl⟩ := mapped _ _ (by unfold tcNeeds at hm; exact hm)
    obtain ⟨j', he, ⟨q, hg, hc⟩, -⟩ := hf
    cases he
    obtain ⟨pc, kd, rfl⟩ := isTcColl_tc hc
    exact notK hg id
  have hjY : (Y).get j = X.get j := appendLanes_get_old hj
  unfold Needs at hmem
  cases hget : (Y).get j with
  | none => simp [hget] at hmem
  | some q =>
  simp only [hget] at hmem
  obtain ⟨pc0, kd⟩ := q
  cases kd
  case shfl =>
    obtain ⟨⟨hs, m, n, q, hat, hx'⟩, p, hp⟩ := maskCase shflClass hmem
    rcases hx' with hxa | ⟨-, ⟨pc, hg⟩, -⟩
    · refine .inr (.inr (.inl ⟨hs, n, ?_, ?_⟩))
      · exact ((maskK_shflClass _ _ _ _).mp hxa.1).2
      · exact ((maskK_shflClass _ _ _ _).mp hat.1).2
    · exact (notK hg id).elim
  case vote => exact .inr (.inr (.inr (maskCase voteClass hmem).1))
  case voteMode => exact .inr (.inr (.inr (maskCase voteClass hmem).1))
  case redux =>
    obtain ⟨-, p, hp⟩ := maskCase reduxClass hmem
    have := hlc
    generalize (ev x.1).kind = k at hp this
    cases k <;> simp only [Kind.LaneColl] at this <;> simp [reduxClass] at hp
  case match_ =>
    obtain ⟨-, p, hp⟩ := maskCase matchClass hmem
    have := hlc
    generalize (ev x.1).kind = k at hp this
    cases k <;> simp only [Kind.LaneColl] at this <;> simp [matchClass] at hp
  case elect mask inst leader =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', pc', ld, he, hg⟩ := hf
    cases he
    exact .inl ⟨pc', pc0, mask, inst, ld, leader, hg, hget⟩
  case warpBar mask inst =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, hg⟩ := hf
    cases he
    exact .inr (.inl ⟨mask, inst, hg, pc0, hget⟩)
  case matrix op own recv =>
    obtain ⟨l, -, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', he, ⟨⟨q, hg, hm⟩, -⟩ | ⟨⟨pc', hg⟩, -⟩⟩ := hf
    · cases he
      obtain ⟨pc, k⟩ := q
      cases k <;> simp only [isMatrix, Bool.false_eq_true] at hm
      exact (notK hg id).elim
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

/-- **Every new dependency enters a new event**, when no new event matches an old one. -/
theorem appendLanes_waits_cases_lane (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    (hfresh : ∀ h ∈ ds, ∀ j : EvId, j.2 < (X.tr j.1).length →
      ¬ WarpMatch L Y (h, (X.tr h).length) j)
    {u v : Ref × Bool} (h : Waits L Y u v) : AppendedNode X ds v ∨ Waits L X u v := by
  have le : X.le Y := le_appendLanes
  have ha := appendLanes_threadAppend (X := X) (ds := ds) (ev := ev)
  have hpres : ∀ i p, (Y).AsyncPresent i p → X.AsyncPresent i p :=
    fun _ _ => (appendLanes_asyncPresent_lane hd hw).mp
  have newj {j : EvId} (hj : j.1 ∈ ds ∧ j.2 = (X.tr j.1).length) {b : Bool} :
      AppendedNode X ds (.thread j, b) :=
    ⟨j.1, hj.1, congrArg Ref.thread (Prod.ext rfl hj.2)⟩
  -- a collective match of a new event with an old one is excluded by freshness
  have nofresh {i j : EvId} (hi : i.1 ∈ ds ∧ i.2 = (X.tr i.1).length)
      (hj : j.2 < (X.tr j.1).length) (hm : WarpMatch L Y i j) : False := by
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
      (fun _ _ => appendLanes_ctaBarK_lane hw) (fun _ _ => appendLanes_ctaBarArrivalK_lane hw)
      i j b b').mp hbar⟩)))
  · subst hi hj
    rcases appendLanes_index_cases his.lt with hio | hin
    · rcases appendLanes_index_cases hjs.lt with hjo | hjn
      · exact .inr (.inr (.inr (.inr (.inl ⟨h1, h2, i, j, rfl, rfl, hwarp, k,
          (appendLanes_shflK_old hio).mp his, (appendLanes_shflK_old hjo).mp hjs⟩))))
      · exact .inl (newj hjn)
    · rcases appendLanes_index_cases hjs.lt with hjo | hjn
      · exact (nofresh hin hjo (.inr (.inr (.inl ⟨hwarp, k, his, hjs⟩)))).elim
      · exact .inl (newj hjn)
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨h1, h2, i, j, hi, hj, hwarp, k,
      (appendLanes_tcK_lane hw).mp hit, (appendLanes_tcK_lane hw).mp hjt⟩)))))
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
      exact (nofresh ⟨hx1, hx2⟩ hjo (appendLanes_witness_new hX hw ⟨hx1, hx2⟩ hjo hwit)).elim
    · refine .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, h2, j, rfl,
        ha.witness hpres ?_ hjn hwit⟩)))))))))
      rintro ⟨x, hx, rfl⟩
      exact hun ⟨x, hx.1, hx.2, rfl⟩
  · subst hi hj
    obtain ⟨hs, mask, inst, ⟨pc, hei⟩, ⟨pc', hej⟩⟩ := hwb
    rcases getOld hej with ⟨hjo, hej'⟩ | hjn
    · rcases getOld hei with ⟨-, hei'⟩ | hin
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, h2,
          i, j, rfl, rfl, hs, mask, inst, ⟨pc, hei'⟩, ⟨pc', hej'⟩⟩))))))))))
      · exact (nofresh hin hjo (.inr (.inl ⟨mask, inst, ⟨pc, hei⟩, ⟨pc', hej⟩⟩))).elim
    · exact .inl (newj hjn)
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1, h2, i, j, hi, hj, appendLanes_synchronizesWith_lane hd hw hms⟩)))))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨i, j, hi, hj, (appendLanes_regWaits_lane hw).mp hrw⟩))))))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨h1, h2, i, j, hi, hj, cta, hpre⟩)))))))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inl ⟨h1, h2, i, j, hi, hj, appendLanes_fenceSync_lane hd hw hfs⟩))))))))))))))
  · obtain ⟨-, -, i, p, rfl, rfl, ⟨q, hq⟩, hap, hm⟩ := his
    have hapX := hpres i p hap
    have hio : i.2 < (X.tr i.1).length :=
      refPresent_issuer_lt hX.effectValidity (f := .async i p) hapX
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inr ⟨h1, h2, h1, h2, i, p, rfl, rfl, ⟨q, by rwa [appendLanes_get_old hio] at hq⟩, hapX,
        hm⟩))))))))))))))

/-- A new arrival waits only for returns. -/
private theorem arrival_to_return_lane (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
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
      (fun _ _ => appendLanes_ctaBarK_lane hw) (fun _ _ => appendLanes_ctaBarArrivalK_lane hw)
      i j _ _).mp hbar⟩)))).elim
  · exact (noOld (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, j, hi, hj,
      (Proof.ExtensionWait.clusterWaits_iff hX le rfl i j _ _).mp hcl⟩))))))))).elim
  · exact hrw.2.1
  · exfalso
    obtain ⟨-, -, i, p, he, rfl, -, hap, -⟩ := his
    cases he
    have : (X.tr h).length < (X.tr h).length :=
      refPresent_issuer_lt hX.effectValidity (f := .async (h, (X.tr h).length) p)
        ((appendLanes_asyncPresent_lane hd hw).mp hap)
    exact Nat.lt_irrefl _ this

/-- **Appending lane collectives that match no old event is a sink frame** for the new events,
given that causality into old events is old. -/
theorem appendLanes_sinkFrame_lane (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hw : ∀ h ∈ ds, (ev h).kind.LaneColl)
    (hfresh : ∀ h ∈ ds, ∀ j : EvId, j.2 < (X.tr j.1).length →
      ¬ WarpMatch L Y (h, (X.tr h).length) j)
    (hv : EffectValidity L Y) (hcl : ClusterHistoryOk L Y)
    (hhb : ∀ i j, j.2 < (X.tr j.1).length → baseCausality L Y i j → baseCausality L X i j) :
    SinkFrame L K A X Y (AppendedNode X ds) := by
  refine appendLanes_threadAppend.sinkFrame hX (fun i b hi => ⟨i.1, hi.1, by rw [← hi.2]⟩)
    (fun i ⟨h, hh, he⟩ => by cases he; exact ⟨hh, rfl⟩)
    (fun _ _ => (appendLanes_asyncPresent_lane hd hw).mp) hhb ⟨fun n => if n.2 then 1 else 0, ?_⟩
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
    refine quiet_return_sink_of_effects hv hcl hget (hw h hh).quiet hlast
      (fun cta j hc => ?_) v hwt
    obtain ⟨pc, grp, dst, act, hold⟩ := Tmem.Pair.Precedes.actual hX.tmemPair hc
    have := len_of_get hold
    simp at this
  | false =>
    have hb := arrival_to_return_lane hX hd hw hwt
    obtain ⟨v, b'⟩ := v
    simp only at hb
    subst hb
    refine ⟨?_, by simp⟩
    rcases appendLanes_waits_cases_lane hX hd hw hfresh hwt with hn | hx
    · exact hn
    · obtain ⟨q, hq⟩ := (waits_present hX.effectValidity hx).1
      have := len_of_get hq
      simp at this

end
end PTX.Step
