-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocResourceWaiting
public import Lemmas.Snoc.ObjectAppend
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Order.WaitingClosure
public import Lemmas.Tmem.AllocResultDependency

@[expose] public section

/-! # Execution-order axioms after appending one thread event

Appending one thread event `X.newId g` (with object histories that only gain records of
that event) is a `SinkFrame` once three kind-specific facts are known: thread causality into
old events is unchanged, no asynchronous stage appears, and asynchronous waits between old
nodes are unchanged. Every other primitive relation between old nodes (rendezvous, object
order, observation, copy release, guards) depends only on old events and old histories,
which the append keeps. The closedness of the new nodes is the kind-specific waiting
analysis of the appended event. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

/-- The appended node of thread `g`. -/
abbrev Execution.newId (X : Execution) (g : Nat) : EvId := (g, (X.tr g).length)

/-- Append one thread event and replace the object histories. -/
def Execution.snocHistory (X : Execution) (g : Nat) (e : Event)
    (r : Nat → Option Ref) (records : Loc → List (MBarrier.Record Ref)) : Execution :=
  { X.snoc g e r with objects := records }

namespace MBarrier

theorem Before.append_iff {log l : List (Record ι)} {u w : ι} (h : ∀ q ∈ l, q.id ≠ w) :
    Before (log ++ l) u w ↔ Before log u w := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l q ih =>
    rw [← List.append_assoc, Before.snoc_iff (h q (by simp))]
    exact ih fun q' hq' => h q' (by simp [hq'])

theorem UpdateBeforeWait.append_iff {log l : List (Record ι)} {u w : ι}
    (h : ∀ q ∈ l, q.id ≠ w) : UpdateBeforeWait (log ++ l) u w ↔ UpdateBeforeWait log u w := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l q ih =>
    rw [← List.append_assoc, UpdateBeforeWait.snoc_iff (h q (by simp))]
    exact ih fun q' hq' => h q' (by simp [hq'])

end MBarrier

/-- `Y` appends the thread events `New` to `X`: every other event, every old trace prefix, the
asynchronous effects and the barrier, cluster, register and Tensor Memory histories are those
of `X`, and object histories only gain records of new events. -/
structure ThreadAppend (X Y : Execution) (New : EvId → Prop) : Prop where
  get : ∀ i, ¬ New i → Y.get i = X.get i
  fresh : ∀ i, New i → X.get i = none
  take : ∀ i : EvId, i.2 < (X.tr i.1).length → (Y.tr i.1).take i.2 = (X.tr i.1).take i.2
  tracePrefix : ∀ h, X.tr h <+: Y.tr h
  async : Y.async = X.async
  tensor : Y.tensor = X.tensor
  barriers : Y.barriers = X.barriers
  clusters : Y.clusters = X.clusters
  tmemHistory : Y.tmemHistory = X.tmemHistory
  tmemPairing : Y.tmemPairing = X.tmemPairing
  tmemPairBlocks : Y.tmemPairBlocks = X.tmemPairBlocks
  objects : ∀ m, ∃ l, Y.objects m = X.objects m ++ l ∧ ∀ q ∈ l, ∃ i, New i ∧ q.id = .thread i

namespace ThreadAppend
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X Y : Execution}
  {New : EvId → Prop}

/-- A reference that is a new event. -/
def NewRef (New : EvId → Prop) (x : Ref) : Prop := ∃ i, New i ∧ x = .thread i

theorem get_ne (ha : ThreadAppend X Y New) {i : EvId} {ev : Event} (h : Y.get i = some ev)
    (hi : ¬ New i) : X.get i = some ev := by rw [← ha.get i hi]; exact h

theorem old_of_ne (ha : ThreadAppend X Y New) {i : EvId} {ev : Event} (h : Y.get i = some ev)
    (hi : ¬ New i) : i.2 < (X.tr i.1).length := len_of_get (ha.get_ne h hi)

theorem not_new (ha : ThreadAppend X Y New) {i : EvId} (h : i.2 < (X.tr i.1).length) :
    ¬ New i := fun hn => by
  have := ha.fresh i hn
  unfold Execution.get at this
  rw [List.getElem?_eq_getElem h] at this
  cases this

theorem old_of_len (ha : ThreadAppend X Y New) {i : EvId} (h : i.2 < (Y.tr i.1).length)
    (hi : ¬ New i) : i.2 < (X.tr i.1).length := by
  refine ha.old_of_ne (ev := (Y.tr i.1)[i.2]) ?_ hi
  unfold Execution.get; exact List.getElem?_eq_getElem h

theorem not_id (ha : ThreadAppend X Y New) (m : Loc) {w : Ref} (hw : ¬ NewRef New w) :
    ∃ l, Y.objects m = X.objects m ++ l ∧ ∀ q ∈ l, q.id ≠ w := by
  obtain ⟨l, hl, hq⟩ := ha.objects m
  refine ⟨l, hl, fun q h' he => hw ?_⟩
  obtain ⟨i, hi, hid⟩ := hq q h'
  exact ⟨i, hi, he ▸ hid⟩

theorem ctaBarK (ha : ThreadAppend X Y New) {v : EvId} {key : Nat} (hv : ¬ New v) :
    CtaBarK L Y v key ↔ CtaBarK L X v key := by
  unfold CtaBarK Execution.IsBarrier; rw [ha.get v hv, ha.barriers]

theorem ctaBarArrivalK (ha : ThreadAppend X Y New) {v : EvId} {key : Nat} (hv : ¬ New v) :
    CtaBarArrivalK L Y v key ↔ CtaBarArrivalK L X v key := by
  unfold CtaBarArrivalK Execution.IsBarArrival; rw [ha.get v hv, ha.barriers]

theorem shflK (ha : ThreadAppend X Y New) {v : EvId} {n : Nat} (hv : ¬ New v) :
    Y.ShflK v n ↔ X.ShflK v n := by
  unfold Execution.ShflK
  rw [ha.get v hv]
  constructor <;> rintro ⟨⟨pc, m, a, b, c, rv, ok, hs⟩, hcnt⟩ <;>
    refine ⟨⟨pc, m, a, b, c, rv, ok, hs⟩, ?_⟩
  · rwa [ha.take v (len_of_get hs)] at hcnt
  · rwa [ha.take v (len_of_get hs)]

theorem tcK (ha : ThreadAppend X Y New) {v : EvId} {k : Nat} (hv : ¬ New v) :
    Y.TcK v k ↔ X.TcK v k := by
  unfold Execution.TcK
  rw [ha.get v hv]
  constructor <;> rintro ⟨⟨ev, hs, hc⟩, hcnt⟩ <;> refine ⟨⟨ev, hs, hc⟩, ?_⟩
  · rwa [ha.take v (len_of_get hs)] at hcnt
  · rwa [ha.take v (len_of_get hs)]

theorem sameRequest (ha : ThreadAppend X Y New) {i j : EvId} (hi : ¬ New i) (hj : ¬ New j) :
    SetMaxNReg.SameRequest L Y i j ↔ SetMaxNReg.SameRequest L X i j := by
  unfold SetMaxNReg.SameRequest SetMaxNReg.Request SetMaxNReg.ordinal
  rw [ha.get i hi, ha.get j hj]
  constructor <;> rintro ⟨hs, ho, pc, inc, n, ei, fi, h1, h2⟩ <;>
    refine ⟨hs, ?_, pc, inc, n, ei, fi, h1, h2⟩
  · rwa [ha.take i (len_of_get h1), ha.take j (len_of_get h2)] at ho
  · rwa [ha.take i (len_of_get h1), ha.take j (len_of_get h2)]

/-- The issuing instruction of a recorded asynchronous update is an old event: the appended
records are records of new thread events. -/
theorem async_issue_old (ha : ThreadAppend X Y New) (hX : Consistent L K A mem0 X) {m : Loc}
    {i : EvId} {p : Part} {y : Ref} (hb : Before (Y.objects m) (.async i p) y) :
    i.2 < (X.tr i.1).length := by
  obtain ⟨a, b, ra, rb, hra, hid, -⟩ := hb
  obtain ⟨l, hl, hq⟩ := ha.objects m
  have hmem := List.mem_of_getElem? hra
  rw [hl] at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · have hp := object_record_present hX.tma hmem
    rw [hid] at hp
    exact refPresent_issuer_lt hX.effectValidity hp
  · obtain ⟨j, -, hj⟩ := hq ra hmem
    rw [hid] at hj; cases hj

/-- A new event lies past the old trace of its thread. -/
theorem new_ge (ha : ThreadAppend X Y New) {j : EvId} (hj : New j) : (X.tr j.1).length ≤ j.2 :=
  Nat.le_of_not_lt fun h => ha.not_new h hj

/-- A group wait at an old event is one of `X`: it reads the event and its trace prefix. -/
theorem groupWaitsFor (ha : ThreadAppend X Y New) {k : GroupWait} {i j : EvId} (hj : ¬ New j)
    (h : GroupWaitsFor Y k i j) : GroupWaitsFor X k i j := by
  cases k with
  | bulk mode =>
    obtain ⟨pc, rem, hget, hobs⟩ := h
    have hx := ha.get_ne hget hj
    refine ⟨pc, rem, hx, ?_⟩
    simpa only [bulkStateBefore, ha.take j (len_of_get hx)] using hobs
  | cpAsync =>
    obtain ⟨pc, rem, hget, hobs⟩ := h
    have hx := ha.get_ne hget hj
    refine ⟨pc, rem, hx, ?_⟩
    simpa only [asyncStateBefore, ha.take j (len_of_get hx)] using hobs

/-- The successful wait of an old event observes in `X` what it observes in the append. -/
theorem waitObserves (ha : ThreadAppend X Y New) {x : Ref} {j : EvId} {m : Loc} {acq : Bool}
    {ws : MbarScope} (hj : ¬ New j) (h : WaitObserves Y x j m acq ws) :
    WaitObserves X x j m acq ws := by
  obtain ⟨⟨pc, q, hget⟩, hu⟩ := h
  obtain ⟨l, hl, hq⟩ := ha.not_id m (w := .thread j) (by rintro ⟨i, hi, he⟩; cases he; exact hj hi)
  rw [hl, UpdateBeforeWait.append_iff hq] at hu
  exact ⟨⟨pc, q, ha.get_ne hget hj⟩, hu⟩

/-- A release update by an old event is one of `X`. -/
theorem releaseUpdate (ha : ThreadAppend X Y New) {x : Ref} {s : MbarScope} {g : Nat}
    (hx : ¬ NewRef New x) (h : ReleaseUpdate Y x s g) : ReleaseUpdate X x s g := by
  rcases h with ⟨j, m, tx, count, rfl, hg, pc, hget⟩ | h
  · exact .inl ⟨j, m, tx, count, rfl, hg, pc, ha.get_ne hget fun hj => hx ⟨j, hj, rfl⟩⟩
  · exact .inr h

theorem lifetimeRecord (ha : ThreadAppend X Y New) {m : Loc} {y : Ref} (hy : ¬ NewRef New y)
    (h : MbarLifetimeRecord Y m y) : MbarLifetimeRecord X m y := by
  obtain ⟨j, rfl, ⟨c, pc, hget⟩ | ⟨pc, hget⟩⟩ := h
  · exact ⟨j, rfl, .inl ⟨c, pc, ha.get_ne hget fun hj => hy ⟨j, hj, rfl⟩⟩⟩
  · exact ⟨j, rfl, .inr ⟨pc, ha.get_ne hget fun hj => hy ⟨j, hj, rfl⟩⟩⟩

theorem syncRecord (ha : ThreadAppend X Y New) {m : Loc} {x : Ref} {s : MbarScope} {g : Nat}
    (hx : ¬ NewRef New x) (h : MbarSyncRecord Y m x s g) : MbarSyncRecord X m x s g := by
  rcases h with ⟨hr, ⟨j, tx, count, rfl, pc, hget⟩ | ha'⟩ | ⟨j, pc, q, rfl, hg, hget⟩
  · exact .inl ⟨ha.releaseUpdate hx hr,
      .inl ⟨j, tx, count, rfl, pc, ha.get_ne hget fun hj => hx ⟨j, hj, rfl⟩⟩⟩
  · exact .inl ⟨ha.releaseUpdate hx hr, .inr ha'⟩
  · exact .inr ⟨j, pc, q, rfl, hg, ha.get_ne hget fun hj => hx ⟨j, hj, rfl⟩⟩

theorem maskK (ha : ThreadAppend X Y New) {Q V : Type} {c : Kind → Option (WarpPart Q V)}
    {v : EvId} {m n : Nat} (hv : ¬ New v) (h : Y.MaskK c v m n) : X.MaskK c v m n := by
  obtain ⟨⟨ev, p, hg, hc, hm⟩, hn⟩ := h
  have hx := ha.get_ne hg hv
  exact ⟨⟨ev, p, hx, hc, hm⟩, by rwa [ha.take v (len_of_get hx)] at hn⟩

theorem maskAt (ha : ThreadAppend X Y New) {Q V : Type} {c : Kind → Option (WarpPart Q V)}
    {v : EvId} {m n : Nat} {q : Q} (hv : ¬ New v) (h : Y.MaskAt c v m n q) :
    X.MaskAt c v m n q := by
  obtain ⟨hk, ev, p, hg, hc, hq⟩ := h
  exact ⟨ha.maskK hv hk, ev, p, ha.get_ne hg hv, hc, hq⟩

theorem maskWait (ha : ThreadAppend X Y New) {Q V : Type} {c : Kind → Option (WarpPart Q V)}
    {u v : EvId} (hu : ¬ New u) (hv : ¬ New v) (h : MaskWait L c Y u v) : MaskWait L c X u v := by
  obtain ⟨hs, m, n, q, hf, he | ⟨hb, ⟨pc, hg⟩, hc⟩⟩ := h
  · exact ⟨hs, m, n, q, ha.maskAt hv hf, .inl (ha.maskAt hu he)⟩
  · have hx := ha.get_ne hg hu
    exact ⟨hs, m, n, q, ha.maskAt hv hf, .inr ⟨hb, ⟨pc, hx⟩,
      by rwa [ha.take u (len_of_get hx)] at hc⟩⟩

theorem matrixK (ha : ThreadAppend X Y New) {v : EvId} {n : Nat} (hv : ¬ New v)
    (h : Y.MatrixK v n) : X.MatrixK v n := by
  obtain ⟨⟨ev, hg, hm⟩, hn⟩ := h
  have hx := ha.get_ne hg hv
  exact ⟨⟨ev, hx, hm⟩, by rwa [ha.take v (len_of_get hx)] at hn⟩

theorem exitedShort (ha : ThreadAppend X Y New) {c : Event → Bool} {v : EvId} {n : Nat}
    (hv : ¬ New v) (h : Y.ExitedShort c v n) : X.ExitedShort c v n := by
  obtain ⟨⟨pc, hg⟩, hn⟩ := h
  exact ⟨⟨pc, ha.get_ne hg hv⟩, le_trans ((ha.tracePrefix v.1).sublist.countP_le) hn⟩

/-- A node need of an old event in the append is filled at an old node as one of `X`: every need
reads the event, the trace prefixes of old events and the histories the append keeps, and an
old object record. -/
theorem witness (ha : ThreadAppend X Y New)
    (hpres : ∀ i p, Y.AsyncPresent i p → X.AsyncPresent i p) {x : Ref} {j : EvId}
    (hx : ¬ NewRef New x) (hj : ¬ New j) (h : Witness L Y x j) : Witness L X x j := by
  obtain ⟨fills, hmem, hp, hf⟩ := h
  have hpX : X.RefPresent x := by
    cases x with
    | thread i =>
      obtain ⟨ev, hev⟩ := hp
      exact ⟨ev, ha.get_ne hev fun hi => hx ⟨i, hi, rfl⟩⟩
    | async i p => exact hpres i p hp
  have hxo : ∀ {i : EvId}, x = .thread i → ¬ New i := fun he hi => hx ⟨_, hi, he⟩
  have hjo := ha.get j hj
  -- the shape of a map-built need list
  have mapped : ∀ {α : Type} (l : List α) (P : α → Ref → Prop),
      Need.node fills ∈ l.map (fun a => Need.node (P a)) → ∃ a ∈ l, fills = P a := by
    intro α l P hm
    obtain ⟨a, ha', he⟩ := List.mem_map.mp hm
    exact ⟨a, ha', (Need.node.inj he).symm⟩
  unfold Needs at hmem
  rw [hjo] at hmem
  cases hget : X.get j with
  | none => simp [hget] at hmem
  | some ev =>
  simp only [hget] at hmem
  suffices key : ∃ fills', Need.node fills' ∈ KindNeeds L X ev.kind j ∧ fills' x by
    obtain ⟨fills', hm, hf'⟩ := key
    exact Witness.of_need L (by simp only [Needs, hget]; exact hm) hpX hf'
  have hjlt : j.2 < (X.tr j.1).length := len_of_get hget
  have htake := ha.take j hjlt
  have maskCase : ∀ {Q V : Type} (c : Kind → Option (WarpPart Q V)),
      Need.node fills ∈ maskNeeds L c Y j →
        ∃ fills', Need.node fills' ∈ maskNeeds L c X j ∧ fills' x := by
    intro Q V c hm
    unfold maskNeeds at hm ⊢
    rw [hjo] at hm
    generalize ((X.get j).bind fun ev => c ev.kind) = o at hm ⊢
    cases o with
    | none => simp at hm
    | some p =>
      obtain ⟨l, hl, rfl⟩ := mapped _ _ hm
      obtain ⟨j', rfl, hw⟩ := hf
      exact ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, j', rfl, ha.maskWait (hxo rfl) hj hw⟩
  have tcCase : Need.node fills ∈ tcNeeds L Y j →
      ∃ fills', Need.node fills' ∈ tcNeeds L X j ∧ fills' x := by
    intro hm
    unfold tcNeeds at hm ⊢
    rw [htake] at hm
    obtain ⟨l, hl, rfl⟩ := mapped _ _ hm
    obtain ⟨j', rfl, hk⟩ := hf
    exact ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, j', rfl, (ha.tcK (hxo rfl)).mp hk⟩
  have groupCase : ∀ k : GroupWait, Need.node fills ∈ groupNeeds Y j k →
      ∃ fills', Need.node fills' ∈ groupNeeds X j k ∧ fills' x := by
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
      obtain ⟨p, hp', rfl⟩ := mapped _ _ hm
      refine ⟨fun y => y = .async (j.1, i) p, List.mem_flatMap.mpr ⟨i, hi, ?_⟩, hf⟩
      simp only [needsIf, ha.groupWaitsFor hj hw, ite_true]
      exact List.mem_map.mpr ⟨p, hp', rfl⟩
    · simp [needsIf, hw] at hm
  have resourceCase : ∀ (group : CtaGroup) (request : Tmem.Request),
      Need.node fills ∈ resourceNeeds L Y j group request →
        ∃ fills', Need.node fills' ∈ resourceNeeds L X j group request ∧ fills' x := by
    intro group request hm
    unfold resourceNeeds at hm ⊢
    rcases List.mem_append.mp hm with hm | hresult
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨f', h1, h2⟩ := tcCase hm
        exact ⟨f', List.mem_append_left _ (List.mem_append_left _ h1), h2⟩
      · refine ⟨fills, List.mem_append_left _ (List.mem_append_right _
          (List.mem_cons_of_mem _ ?_)), hf⟩
        rcases List.mem_cons.mp hm with h | hm
        · cases h
        have hMW : Tmem.Pair.MustWait Y j = Tmem.Pair.MustWait X j := by
          unfold Tmem.Pair.MustWait
          rw [hjo, ha.tmemPairBlocks]
        have hRR : ReuseRelease L Y j = ReuseRelease L X j := by
          funext j1
          unfold ReuseRelease
          rw [ha.tmemHistory]
        rw [hMW, hRR, ha.tmemHistory, ha.tmemPairing] at hm
        unfold needsIf at hm ⊢
        split_ifs at hm ⊢
        · rcases List.mem_cons.mp hm with h | hm
          · cases h
          exact List.mem_cons_of_mem _ hm
        · simp at hm
    · have hnode := Tmem.Pair.allocResultNeeds_transport (Y := X) L hresult
      obtain rfl := Need.node.inj (Tmem.Pair.allocResultNeeds_node L hresult)
      exact ⟨_, List.mem_append_right _ hnode, hf.of_tracePrefix ha.tracePrefix hpX hjlt⟩
  obtain ⟨pc, k⟩ := ev
  cases k
  case shfl => exact maskCase shflClass hmem
  case vote => exact maskCase voteClass hmem
  case voteMode => exact maskCase voteClass hmem
  case redux => exact maskCase reduxClass hmem
  case match_ => exact maskCase matchClass hmem
  case elect mask inst leader =>
    obtain ⟨l, hl, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', pc', ld, rfl, hg⟩ := hf
    exact ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, j', pc', ld, rfl, ha.get_ne hg (hxo rfl)⟩
  case warpBar mask inst =>
    obtain ⟨l, hl, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', rfl, pc', hg⟩ := hf
    exact ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, j', rfl, pc', ha.get_ne hg (hxo rfl)⟩
  case matrix op own recv =>
    simp only [KindNeeds, htake] at hmem
    obtain ⟨l, hl, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', rfl, hk | hk⟩ := hf
    · exact ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, j', rfl, .inl (ha.matrixK (hxo rfl) hk)⟩
    · exact ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, j', rfl, .inr (ha.exitedShort (hxo rfl) hk)⟩
  case setMaxReg inc n inst =>
    obtain ⟨l, hl, rfl⟩ := mapped _ _ hmem
    obtain ⟨j', rfl, hs⟩ := hf
    exact ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, j', rfl, (ha.sameRequest hj (hxo rfl)).mp hs⟩
  case bar id count mode =>
    simp only [KindNeeds, ctaBarNeeds, ctaBarWarpNeeds, CtaBarCounted, CtaBarDone, ha.barriers,
      ha.ctaBarK hj] at hmem
    exact ⟨fills, hmem, hf⟩
  case cluster op =>
    simp only [KindNeeds, clusterNeeds, clusterWarpNeeds, ClusterCounted, ha.clusters] at hmem
    exact ⟨fills, hmem, hf⟩
  case bulkWait mode rem => exact groupCase (.bulk mode) hmem
  case asyncWait rem => exact groupCase .cpAsync hmem
  case wait m q ok acq sc =>
    cases ok
    · simp [KindNeeds] at hmem
    simp only [KindNeeds, ite_true, pollNeeds] at hmem ⊢
    obtain ⟨r, hr, hm⟩ := List.mem_flatMap.mp hmem
    by_cases hob : MbarObserved Y r.id (.thread j)
    swap
    · simp [needsIf, hob] at hm
    simp only [needsIf, hob, ite_true] at hm
    obtain rfl : fills = (· = r.id) := (Need.node.inj (List.mem_singleton.mp hm))
    subst hf
    obtain ⟨l, hl, hq⟩ := ha.objects m
    rw [hl] at hr
    rcases List.mem_append.mp hr with hr | hr
    · refine ⟨fun y => y = r.id, List.mem_flatMap.mpr ⟨r, hr, ?_⟩, rfl⟩
      have hob' : MbarObserved X r.id (.thread j) := by
        obtain ⟨-, j', m', acq', ws, hw, hwo, hc⟩ := hob
        obtain rfl : j' = j := (Ref.thread.inj hw).symm
        obtain ⟨l', hl', -⟩ := ha.objects m'
        exact ⟨hpX, j', m', acq', ws, rfl, ha.waitObserves hj hwo,
          fun r' hr' hid => hc r' (by rw [hl']; exact List.mem_append_left _ hr') hid⟩
      simp only [needsIf, hob', ite_true, List.mem_singleton]
    · obtain ⟨i, hi, hid⟩ := hq r hr
      exact (hx ⟨i, hi, hid⟩).elim
  case tc t =>
    cases t
    case ld => exact tcCase hmem
    case st => exact tcCase hmem
    case waitLd => exact tcCase hmem
    case waitSt => exact tcCase hmem
    case resource group dst request => exact resourceCase group request hmem
    all_goals simp [KindNeeds] at hmem
  all_goals simp [KindNeeds] at hmem

/-- A stage order hop of the append between present stages is one of `X`: its clauses read the
presence of the two stages and the tracking of an MMA by a commit or of a `cp.async` by an
arrive-on, which read old events. -/
theorem stageEdge (ha : ThreadAppend X Y New) (hX : Consistent L K A mem0 X)
    (hpres : ∀ i p, Y.AsyncPresent i p → X.AsyncPresent i p) {e f : Ref}
    (h : StageEdge Y e f) : StageEdge X e f := by
  have hold : ∀ {i p}, Y.AsyncPresent i p → ¬ New i := fun hp =>
    ha.not_new (refPresent_issuer_lt hX.effectValidity (f := .async _ _) (hpres _ _ hp))
  have hmma : ∀ {i j p q}, Y.AsyncPresent i p → Y.AsyncPresent j q → TracksMma Y i j →
      TracksMma X i j := by
    rintro i j p q hi hj ⟨h1, h2, (⟨d, s, ac, mk, pc, hg⟩ | ⟨c, pc, hg⟩ | ⟨s, pc, hg⟩), s', pc', hc⟩
    · exact ⟨h1, h2, .inl ⟨d, s, ac, mk, pc, ha.get_ne hg (hold hi)⟩, s', pc',
        ha.get_ne hc (hold hj)⟩
    · exact ⟨h1, h2, .inr (.inl ⟨c, pc, ha.get_ne hg (hold hi)⟩), s', pc', ha.get_ne hc (hold hj)⟩
    · exact ⟨h1, h2, .inr (.inr ⟨s, pc, ha.get_ne hg (hold hi)⟩), s', pc',
        ha.get_ne hc (hold hj)⟩
  have hcp : ∀ {i j p q}, Y.AsyncPresent i p → Y.AsyncPresent j q → TracksCpAsync Y i j →
      TracksCpAsync X i j := by
    rintro i j p q hi hj ⟨h1, h2, ⟨s, ⟨pc, hg⟩, hs⟩, m, noinc, pc', hc⟩
    exact ⟨h1, h2, ⟨s, ⟨pc, ha.get_ne hg (hold hi)⟩, hs⟩, m, noinc, pc', ha.get_ne hc (hold hj)⟩
  unfold StageEdge at h ⊢
  split at h
  all_goals first
    | exact h.elim
    | exact ⟨h.1, hpres _ _ h.2.1, hpres _ _ h.2.2⟩
    | exact ⟨h.1, h.2.1, hpres _ _ h.2.2.1, hpres _ _ h.2.2.2⟩
    | exact ⟨hmma h.2.1 h.2.2 h.1, hpres _ _ h.2.1, hpres _ _ h.2.2⟩
    | exact ⟨hcp h.2.1 h.2.2 h.1, hpres _ _ h.2.1, hpres _ _ h.2.2⟩

/-- **An append of thread events is a sink frame** for `S` (the new events, and possibly
terminal return nodes), given the closedness of `S` and causality into old events. Every other
row (stage order, dependency steps,
observations, object orders, EXT-ASYNC-OBJECT) reads old events, old trace prefixes, old object
records and histories the append keeps. -/
theorem orderTransport (ha : ThreadAppend X Y New) (hX : Consistent L K A mem0 X)
    {S : Ref × Bool → Prop} (hS : ∀ i b, New i → S (.thread i, b))
    (hSi : ∀ i, S (.thread i, false) → New i)
    (hpres : ∀ i p, Y.AsyncPresent i p → X.AsyncPresent i p)
    (hhb : ∀ i j, j.2 < (X.tr j.1).length → baseCausality L Y i j → baseCausality L X i j)
    (hback : ∀ u v, stageCausality L Y u v → ¬ S v → ¬ S u) :
    SinkFrame.Transport L K A X Y S := by
  have ne : ∀ {x : Ref} {b : Bool}, ¬ S (x, b) → ¬ NewRef New x := by
    rintro x b h ⟨i, hi, rfl⟩; exact h (hS i b hi)
  have neId : ∀ {i : EvId} {b : Bool}, ¬ S (.thread i, b) → ¬ New i :=
    fun h hi => h (hS _ _ hi)
  have presentF : ∀ {x : Ref}, ¬ NewRef New x → Y.RefPresent x → X.RefPresent x := by
    intro x hx hp
    cases x with
    | thread i =>
      obtain ⟨ev, hev⟩ := hp
      exact ⟨ev, ha.get_ne hev fun hi => hx ⟨i, hi, rfl⟩⟩
    | async i p => exact hpres i p hp
  have objectF : ∀ o u v, ¬ S u → ¬ S v → ObjectOrder L Y o u v → ObjectOrder L X o u v := by
    rintro o ⟨x, b⟩ ⟨y, b'⟩ hu hv h
    cases o with
    | mbar m =>
      obtain ⟨h1, h2, hb⟩ := h
      obtain ⟨l, hl, hq⟩ := ha.not_id m (ne hv)
      rw [hl, Before.append_iff hq] at hb
      exact ⟨h1, h2, hb⟩
    | ctaBar c id =>
      obtain ⟨h1, h2, i, j, rfl, rfl, ⟨ev, hi⟩, ⟨ev', hj⟩, rest⟩ := h
      rw [ha.barriers] at rest
      exact ⟨h1, h2, i, j, rfl, rfl, ⟨ev, ha.get_ne hi (neId hu)⟩,
        ⟨ev', ha.get_ne hj (neId hv)⟩, rest⟩
    | cluster c =>
      obtain ⟨i, j, rfl, rfl, ⟨ev, hi⟩, ⟨ev', hj⟩, rest⟩ := h
      rw [ha.clusters] at rest
      exact ⟨i, j, rfl, rfl, ⟨ev, ha.get_ne hi (neId hu)⟩,
        ⟨ev', ha.get_ne hj (neId hv)⟩, rest⟩
    | tmem cta =>
      obtain ⟨h1, h2, i, j, rfl, rfl, hp⟩ := h
      unfold Tmem.Pair.Precedes at hp
      rw [ha.tmemHistory] at hp
      exact ⟨h1, h2, i, j, rfl, rfl, hp⟩
  have oldW : ∀ {w f : EvId}, po Y w f → ¬ New f → w.2 < (X.tr w.1).length ∧ po X w f := by
    intro w f hpo hf
    have hfo := ha.old_of_len hpo.2.2.1 hf
    have := hpo.2.1
    exact ⟨by rw [hpo.1]; omega,
      (po_congr hfo hpo.2.2.1 (fun x hx => ha.get x (ha.not_new hx))).mp hpo⟩
  have stageOrderF : ∀ {u v : Ref × Bool}, ¬ S u → ¬ S v → StageOrder Y u v → StageOrder X u v := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ hu hv (⟨rfl, hb, hb', hp⟩ | ⟨hb, hb', hs⟩)
    · exact .inl ⟨rfl, hb, hb', presentF (ne hu) hp⟩
    · exact .inr ⟨hb, hb', ha.stageEdge hX hpres hs⟩
  have hstage : ∀ u v, ¬ S u → ¬ S v → stageCausality L Y u v →
      Relation.TransGen (stageCausality L X) u v := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ hu hv (hs | ⟨hb, hb', i, j, rfl, rfl, hc⟩ | ⟨hb, hb', j, rfl, hc⟩)
    · exact .single (.inl (stageOrderF hu hv hs))
    · have hj := neId hv
      exact .single (.inr (.inl ⟨hb, hb', i, j, rfl, rfl,
        hhb i j (ha.old_of_len (baseCausality_events hc).2 hj) hc⟩))
    · obtain ⟨i, p, w, ws, rfl, hp, ⟨n, m, hnot, hwo⟩, hsc, hpo⟩ := hc
      obtain ⟨hwo', hpo'⟩ := oldW hpo (neId hv)
      have hw : ¬ New w := ha.not_new hwo'
      have hnot' : AsyncCopy.Notifies X i p n m := by
        rcases hp with rfl | rfl
        · obtain ⟨rfl, bytes, s, hs', hn, hm, hbytes⟩ := hnot
          rw [ha.async] at hn
          have hio : i.2 < (X.tr i.1).length :=
            refPresent_issuer_lt hX.effectValidity (f := .async i (.notify .copy)) hn
          have hiss : issuedBy Y i = issuedBy X i := by
            unfold issuedBy; rw [ha.get i (ha.not_new hio)]
          exact ⟨rfl, bytes, s, hiss ▸ hs', hn, hm, hbytes⟩
        · obtain ⟨rfl, obs, addr, ht, ⟨pc, hti⟩, hm, hn⟩ := hnot
          rw [ha.tensor] at ht
          have hio : i.2 < (X.tr i.1).length :=
            refPresent_issuer_lt hX.effectValidity (f := .async i (.notify .load)) ⟨obs, ht, hn⟩
          exact ⟨rfl, obs, addr, ht, ⟨pc, ha.get_ne hti (ha.not_new hio)⟩, hm, hn⟩
      exact .single (.inr (.inr ⟨hb, hb', j, rfl,
        ⟨i, p, w, ws, rfl, hp, ⟨n, m, hnot', ha.waitObserves hw hwo⟩, hsc, hpo'⟩⟩))
  have hdep : ∀ u v, ¬ S u → ¬ S v → DepStep L K Y u v →
      Relation.TransGen (DepStep L K X) u v := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ hu hv (hs | ⟨hb, hb', i, p, rfl, rfl, hpr, hap, hm⟩ |
      ⟨hb, hb', j, rfl, hw⟩ | ⟨hb, hb', w, j, rfl, rfl, ⟨ht1, ht2, ht3⟩, hr⟩)
    · exact .single (.inl (stageOrderF hu hv hs))
    · exact .single (.inr (.inl ⟨hb, hb', i, p, rfl, rfl, presentF (ne hu) hpr, hpres i p hap, hm⟩))
    · exact .single (.inr (.inr (.inl ⟨hb, hb', j, rfl,
        ha.witness hpres (ne hu) (neId hv) hw⟩)))
    · have hj := neId hv
      have hjo := ha.old_of_len ht3 hj
      have hwn : ¬ New w := ha.not_new (by rw [ht1]; omega)
      have htb : TraceBefore X w j := ⟨ht1, ht2, hjo⟩
      refine .single (.inr (.inr (.inr ⟨hb, hb', w, j, rfl, rfl, htb, ?_⟩)))
      rw [ha.get w hwn] at hr
      revert hr
      cases (X.get w).map fun ev => ev.kind.resume with
      | none => exact id
      | some rs =>
        cases rs with
        | blocking => exact id
        | observing =>
          rintro ⟨pc, exit, m, q, acq, sc, hg, hc, -⟩
          exact ⟨pc, exit, m, q, acq, sc, ha.get_ne hg hwn, hc, htb⟩
        | _ => exact id
  have hinit : InitFenceOrdered L Y := by
    intro m init w y hs ht hb
    obtain ⟨count, fence, arrival, pc, pca, release, aligned, pcw, alignedw, ⟨pci, hmi⟩, hsp,
      hcta, hf, h1, h2, h3, h4, harr, hw, c, phase, hac, hwc⟩ := hs
    rw [ha.clusters] at hac hwc
    obtain ⟨pcx, alx, hax⟩ := hX.cluster.arrival_present hac
    have hao := len_of_get hax
    have hfo : fence.2 < (X.tr fence.1).length := by rw [h3]; omega
    have hio : init.2 < (X.tr init.1).length := by rw [h1, h3]; omega
    have hin : ¬ New init := ha.not_new hio
    obtain ⟨l, hl, hq⟩ := ha.not_id m (w := .thread init)
      (by rintro ⟨i, hi, he⟩; cases he; exact hin hi)
    rw [hl, Before.append_iff hq] at hb
    have hyo : ¬ New y.issuer := by
      obtain ⟨a, b, ra, rb, hra, hid, -⟩ := hb
      have hp := object_record_present hX.tma (List.mem_of_getElem? hra)
      rw [hid] at hp
      exact ha.not_new (refPresent_issuer_lt hX.effectValidity hp)
    obtain ⟨hwS, htX⟩ := SinkFrame.old_path_direct hback hstage ht (fun hS' => hyo (hSi _ hS'))
    have hwn : ¬ New w := neId hwS
    exact hX.initFence m init w y ⟨count, fence, arrival, pc, pca, release, aligned, pcw, alignedw,
      ⟨pci, ha.get_ne hmi hin⟩, hsp, hcta, ha.get_ne hf (ha.not_new hfo), h1, h2, h3, h4,
      ha.get_ne harr (ha.not_new hao), ha.get_ne hw hwn, c, phase, hac, hwc⟩ htX hb
  refine
    { cause := hstage
      observed := ?_
      object := objectF
      objectSync := ?_
      dep := hdep
      issue := fun m i p y hb hi =>
        (ha.not_new (ha.async_issue_old hX hb) (hSi i hi)).elim
      asyncSelf := ?_
      asyncObserved := ?_
      initFence := hinit
      get := fun e h => ha.get e (neId h) }
  · rintro x w hx hw (⟨⟨hp, j, m, acq, ws, rfl, hob, hcnt⟩, j', m', pc, q, ws', us, g, hw2, hget,
      hrel, hsc⟩ | ⟨i, p, j, k, rfl, rfl, hp, hgw, hgs⟩)
    · cases hw2
      have hj : ¬ New j := neId hw
      obtain ⟨l, hl, -⟩ := ha.objects m
      refine .inl ⟨⟨presentF (ne hx) hp, j, m, acq, ws, rfl, ha.waitObserves hj hob,
        fun r hr hid => hcnt r (by rw [hl]; exact List.mem_append_left _ hr) hid⟩,
        j, m', pc, q, ws', us, g, rfl, ha.get_ne hget hj, ha.releaseUpdate (ne hx) hrel, hsc⟩
    · have hpx := hpres i p hp
      have hio := refPresent_issuer_lt hX.effectValidity (f := .async i p) hpx
      have hst : GroupWaitStages Y i k = GroupWaitStages X i k := by
        unfold GroupWaitStages; rw [ha.get i (ha.not_new hio)]
      exact .inr ⟨i, p, j, k, rfl, rfl, hpx, ha.groupWaitsFor (neId hw) hgw, hst ▸ hgs⟩
  · rintro o u v hu hv h
    cases o with
    | mbar m =>
      obtain ⟨ho, hs⟩ := h
      refine ⟨objectF (.mbar m) u v hu hv ho, ?_⟩
      rcases hs with ⟨s, g, s', g', h1, h2, hm⟩ | hl | hl | hsame
      · exact .inl ⟨s, g, s', g', ha.syncRecord (ne hu) h1, ha.syncRecord (ne hv) h2, hm⟩
      · exact .inr (.inl (ha.lifetimeRecord (ne hu) hl))
      · exact .inr (.inr (.inl (ha.lifetimeRecord (ne hv) hl)))
      · exact .inr (.inr (.inr hsame))
    | ctaBar c id => exact objectF (.ctaBar c id) u v hu hv h
    | cluster c => exact objectF (.cluster c) u v hu hv h
    | tmem cta => exact objectF (.tmem cta) u v hu hv h
  · intro m i p y hb
    have hio := ha.async_issue_old hX hb
    by_cases hy : NewRef New y
    · obtain ⟨j, hj, rfl⟩ := hy
      rintro ⟨j', he, h1, h2⟩
      cases he
      have := ha.new_ge hj
      rw [h1] at this
      omega
    · obtain ⟨l, hl, hq⟩ := ha.not_id m hy
      rw [hl, Before.append_iff hq] at hb
      exact (hX.asyncObject m i p y hb).1
  · rintro m i p y hip hy (hl | ⟨j, ws, rfl, hob⟩)
    · exact .inl (ha.lifetimeRecord (ne hy) hl)
    · exact .inr ⟨j, ws, rfl, ha.waitObserves (neId hy) hob⟩

theorem sinkFrame (ha : ThreadAppend X Y New) (hX : Consistent L K A mem0 X)
    {S : Ref × Bool → Prop} (hS : ∀ i b, New i → S (.thread i, b))
    (hSi : ∀ i, S (.thread i, false) → New i)
    (hpres : ∀ i p, Y.AsyncPresent i p → X.AsyncPresent i p)
    (hhb : ∀ i j, j.2 < (X.tr j.1).length → baseCausality L Y i j → baseCausality L X i j)
    (closed : ∃ rank : Ref × Bool → Nat, ∀ u v, Waits L Y u v → S u → S v ∧ rank u < rank v) :
    SinkFrame L K A X Y S := by
  obtain ⟨rank, hrank⟩ := closed
  have hback : ∀ u v, stageCausality L Y u v → ¬ S v → ¬ S u := by
    intro u v h hv hu
    exact hv (SinkFrame.closed_path hrank (fun _ _ h => stageCausality.waits h) (.single h) hu).1
  exact (ha.orderTransport hX hS hSi hpres hhb hback).sinkFrame ⟨rank, hrank⟩

end ThreadAppend

section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- The object histories of `Y` only gain records of the appended event. -/
def SnocRecords (X : Execution) (g : Nat) (records : Loc → List (MBarrier.Record Ref)) :
    Prop :=
  ∀ m, ∃ l, records m = X.objects m ++ l ∧ ∀ q ∈ l, q.id = .thread (X.newId g)

theorem SnocRecords.same : SnocRecords X g X.objects :=
  fun _ => ⟨[], by simp, by simp⟩

theorem SnocRecords.append {m : Loc} {rec : MBarrier.Record Ref}
    (hid : rec.id = .thread (X.newId g)) :
    SnocRecords X g (fun l => if l = m then X.objects m ++ [rec] else X.objects l) := by
  intro l
  by_cases hl : l = m
  · subst l; exact ⟨[rec], by simp, by simpa using hid⟩
  · exact ⟨[], by simp [hl], by simp⟩

variable {records : Loc → List (MBarrier.Record Ref)}

theorem SnocRecords.not_id (h : SnocRecords X g records) (m : Loc) {w : Ref}
    (hw : w ≠ .thread (X.newId g)) :
    ∃ l, records m = X.objects m ++ l ∧ ∀ q ∈ l, q.id ≠ w := by
  obtain ⟨l, hl, hq⟩ := h m
  exact ⟨l, hl, fun q h' he => hw (he ▸ hq q h')⟩

/-- An mbarrier synchronization into an old event is old: its arrival is recorded in an old
history, so it is an old event. -/
theorem msync_snocHistory_old (hX : Consistent L K A mem0 X) (hrec : SnocRecords X g records)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (h : MSync L (X.snocHistory g e r records) a b) : MSync L X a b := by
  obtain ⟨x, w, m, rs, ws, ⟨tx, count, pc, hp⟩, ⟨⟨pcw, parity, hw⟩, hu⟩, hsc, hwf, hwlt, _, hxe,
    hle⟩ := h
  have hwo : w.2 < (X.tr w.1).length := by rw [hwf]; omega
  have hwn : (Ref.thread w) ≠ .thread (X.newId g) := by
    intro he; cases he; simp at hwo
  obtain ⟨l, hl, hq⟩ := hrec.not_id m hwn
  change UpdateBeforeWait (records m) _ _ at hu
  rw [hl, UpdateBeforeWait.append_iff hq] at hu
  have hxo : x.2 < (X.tr x.1).length := by
    obtain ⟨i, -, q, -, -, hi, hid, -⟩ := hu
    have hpr := object_record_present hX.tma (List.mem_of_getElem? hi)
    rw [hid] at hpr
    exact refPresent_issuer_lt hX.effectValidity hpr
  change (X.snoc g e r).get x = _ at hp
  change (X.snoc g e r).get w = _ at hw
  exact ⟨x, w, m, rs, ws, ⟨tx, count, pc, by rwa [snoc_get_old hxo] at hp⟩,
    ⟨⟨pcw, parity, by rwa [snoc_get_old hwo] at hw⟩, hu⟩, hsc, hwf, hwlt, hbo, hxe, hle⟩

/-- **Causality into an old event is old** after an append that is no `fence.sc` and gives no
old warp barrier a new partner: barrier phases, cluster phases and mbarrier synchronizations into
old events are recorded in old histories, and an old acquire read reads from an old write. -/
theorem baseCausality_snocHistory_old (hX : Consistent L K A mem0 X)
    (hrec : SnocRecords X g records)
    (hfresh : ∀ mask inst, e.kind = .warpBar mask inst → ∀ j pc, j.2 + 1 < (X.tr j.1).length →
      X.get j = some ⟨pc, .warpBar mask inst⟩ → ¬ SameWarp L g j.1)
    (hsc : ∀ s, e.kind ≠ .fence .sc s)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (h : baseCausality L (X.snocHistory g e r records) a b) : baseCausality L X a b := by
  refine baseCausality_old_of_step (fun {a b} hbo h => ?_) h hbo
  have step := snoc_step_old_of (g := g) (e := e) (r := r) (a := a) hX.cluster (.of_rfWf hX.rf)
    (fun _ _ => snoc_ctaBarK_history hX.ctaBar)
    (fun _ _ => snoc_ctaBarArrivalK_history hX.ctaBar) hbo
    (msync_snocHistory_old (a := a) (records := X.objects) hX SnocRecords.same hbo) hfresh hsc
  rcases h with h | h | h | h | h | h | h
  · exact step (.inl h)
  · exact step (.inr (.inl h))
  · exact .inr (.inr (.inl (msync_snocHistory_old hX hrec hbo h)))
  · exact step (.inr (.inr (.inr (.inl h))))
  · exact step (.inr (.inr (.inr (.inr (.inl h)))))
  · exact step (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  · exact step (.inr (.inr (.inr (.inr (.inr (.inr h))))))

/-- The causality frame for an ordinary appended event (no elect, warp barrier, register
request, `fence.sc` or releasing write). -/
theorem baseCausality_snocHistory_ordinary (hX : Consistent L K A mem0 X)
    (hrec : SnocRecords X g records)
    (hk : e.kind.Ordinary) (i j : EvId) (hj : j.2 < (X.tr j.1).length)
    (h : baseCausality L (X.snocHistory g e r records) i j) : baseCausality L X i j :=
  baseCausality_snocHistory_old hX hrec (fun _ _ he => by simp [Kind.Ordinary, he] at hk)
    (fun _ he => by simp [Kind.Ordinary, he] at hk) hj h

/-- Appending one event with histories that only gain its records is a thread append. -/
theorem SnocRecords.threadAppend (hrec : SnocRecords X g records) :
    ThreadAppend X (X.snocHistory g e r records) (· = X.newId g) where
  get i hi := by
    change (X.snoc g e r).get i = _
    rw [snoc_get, ite_eq_right hi]
  fresh i hi := by subst hi; exact List.getElem?_eq_none (le_refl _)
  take i hi := snoc_take (e := e) (r := r) hi.le
  tracePrefix h := (le_snoc (g := g) (e := e) (r := r)).1 h
  async := rfl
  tensor := rfl
  barriers := rfl
  clusters := rfl
  tmemHistory := rfl
  tmemPairing := rfl
  tmemPairBlocks := rfl
  objects m := by
    obtain ⟨l, hl, hq⟩ := hrec m
    exact ⟨l, hl, fun q h => ⟨_, rfl, hq q h⟩⟩

/-- The new nodes are closed when the appended event's only outgoing waiting edge is its own
issue-to-completion step. -/
theorem snoc_closed {Y : Execution} {n : EvId}
    (hfrom : ∀ b v, Waits L Y (.thread n, b) v → b = false ∧ v = (.thread n, true)) :
    ∃ rank : Ref × Bool → Nat, ∀ u v, Waits L Y u v →
      (fun x : Ref × Bool => x.1 = .thread n) u →
      (fun x : Ref × Bool => x.1 = .thread n) v ∧ rank u < rank v := by
  refine ⟨fun x => if x.2 then 1 else 0, ?_⟩
  rintro ⟨u, b⟩ v h (rfl : u = _)
  obtain ⟨rfl, rfl⟩ := hfrom b v h
  simp

/-- **Appending one thread event is a sink frame**, given the closedness of `S` (the new nodes,
and possibly terminal return nodes) and causality into old events. -/
theorem snoc_sinkFrame (hX : Consistent L K A mem0 X) {S : Ref × Bool → Prop}
    (hS : ∀ n : Ref × Bool, n.1 = .thread (X.newId g) → S n)
    (hSi : ∀ i, S (.thread i, false) → i = X.newId g)
    (hrec : SnocRecords X g records)
    (hpres : ∀ i p, (X.snoc g e r).AsyncPresent i p → X.AsyncPresent i p)
    (hhb : ∀ i j, j.2 < (X.tr j.1).length → baseCausality L (X.snocHistory g e r records) i j →
      baseCausality L X i j)
    (closed : ∃ rank : Ref × Bool → Nat, ∀ u v, Waits L (X.snocHistory g e r records) u v →
      S u → S v ∧ rank u < rank v) :
    SinkFrame L K A X (X.snocHistory g e r records) S :=
  hrec.threadAppend.sinkFrame hX (fun _ _ h => hS _ (by rw [h])) hSi hpres hhb closed

/-- The append with unchanged object histories, for `S` the two new nodes. -/
theorem snoc_sinkFrame_new (hX : Consistent L K A mem0 X)
    (hpres : ∀ i p, (X.snoc g e r).AsyncPresent i p → X.AsyncPresent i p)
    (hhb : ∀ i j, j.2 < (X.tr j.1).length → baseCausality L (X.snoc g e r) i j →
      baseCausality L X i j)
    (hfrom : ∀ b v, Waits L (X.snoc g e r) (.thread (X.newId g), b) v →
      b = false ∧ v = (.thread (X.newId g), true)) :
    SinkFrame L K A X (X.snoc g e r) (fun x => x.1 = .thread (X.newId g)) :=
  snoc_sinkFrame (records := X.objects) hX (fun _ h => h) (fun _ h => Ref.thread.inj h)
    SnocRecords.same hpres hhb (snoc_closed hfrom)

end
end
end PTX
