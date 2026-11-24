-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierAppendFrame
public import Lemmas.CtaBarrier.CtaBarrierHistoryOrder
public import Lemmas.CtaBarrier.CtaBarrierReplaceOrder
public import Lemmas.CtaBarrier.CtaBarrierGeneration
public import Lemmas.CtaBarrier.CtaBarrierHistory
public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Lemmas.CtaBarrier.CtaBarrierTraceHistory
public import Lemmas.MBarrier.BarrierWaitingSources
public import Lemmas.Order.WaitingClosure
public import Lemmas.Snoc.Collectives
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Tmem.TmemPairCompletionFrame
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Protocol.NamedBarLedger
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-! # Named CTA barriers: appended releases and arrival counts

A named CTA barrier resource is a checked list of records, one per warp collective arrival
and one per exit (`CtaBarrier.Record`). The history is explicit: a record is appended when a
warp's collective arrival is performed, and nothing is appended for a release by itself.
A generation is released exactly when some record completes it (`CtaBarrier.Released`,
read by replaying the history). The record that completes a generation is therefore the
last warp arrival of that generation.

An arrival event that has a later event of its thread has returned, so its needs are filled
(`DependencyOk.ready`): its warp needs name its record (`recorded_of_returned`). So an arrival
that is only present as an event, and is not recorded, is the last event of its thread.

`release_append` appends a suffix of arrival records to one CTA's history. If the extended
history is checked, the result is consistent, extends the old execution with the same size,
and stays maximal when the old one is. The CTA barrier relations gain edges only into issue
nodes of the suffix and into return nodes of terminal arrivals, so the execution-order axioms
transfer through the frame of those nodes (`suffix_sinkFrame`). The needs of a returned event
read only records of the old prefix, so readiness and the dependency steps between old nodes are
those of the old execution (`ready_append`, `dep_append`).

An arrival present only as an event has no record, so the progress layer appends its records
first (`release_append`). -/

namespace PTX.Step.CtaBar
open PTX AsyncCopy
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- Rank of the waiting nodes of a suffix: issues of the suffix refs in record order, then every
return node above them. -/
def rankOf (refs : List EvId) : AsyncCopy.Ref × Bool → Nat
  | (.thread e, false) => refs.idxOf e
  | (_, true) => refs.length + 1
  | _ => 0

/-- A recorded generation-arrival is a record of its CTA history. -/
theorem mem_refs_of_generationOf {α : Type} {block : Nat} {h : List (CtaBarrier.Record α)}
    {e : α} {id g : Nat} (hg : CtaBarrier.GenerationOf block h e id g) :
    ∃ r ∈ h, e ∈ r.refs := by
  obtain ⟨i, s, warp, count, lanes, g', hi, -, he, -, -, -⟩ := hg
  exact ⟨_, List.mem_of_getElem? hi, List.mem_map.mpr ⟨(g', e), he, rfl⟩⟩

/-! ## Needs of old events after appending records

Appending records to a CTA's history changes the needs of a CTA barrier arrival of that CTA only
through the history. A returned arrival is already recorded (its warp needs name its record), and
for a `bar.sync` its generation is already released. So every record that one of its needs reads
lies in the old prefix: its needs are those of `X`. -/

/-- The history of CTA `d` after appending to CTA `c` is the old history followed by the appended
records (none when `d ≠ c`). -/
theorem withCtaHistory_append (X : Execution) (c d : Nat)
    (suffix : List (CtaBarrier.Record EvId)) :
    ∃ s, (X.withCtaHistory c (X.barriers c ++ suffix)).barriers d = X.barriers d ++ s := by
  by_cases hd : d = c
  · subst hd
    exact ⟨suffix, withCtaHistory_barriers_self X d _⟩
  · exact ⟨[], by rw [withCtaHistory_barriers_ne X _ hd, List.append_nil]⟩

/-- An event of the launch: a thread with an event lies in the launch. -/
theorem thread_lt_of_get (hX : Consistent L K A mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : e.1 < L.threads := by
  have hlt : e.2 < (X.tr e.1).length := len_of_get he
  by_contra hn
  rw [hX.outside e.1 (by omega)] at hlt
  simp at hlt

/-- **A returned CTA barrier arrival of either form is recorded**: the warp need of its first
lane names a record that contains it. -/
theorem recorded_of_returned (hX : Consistent L K A mem0 X) {e : EvId} {pc id : Nat}
    {cnt : Option Nat} {m : BarMode} (he : X.get e = some ⟨pc, .bar id cnt m⟩)
    (hlt : e.2 + 1 < (X.tr e.1).length) :
    ∃ (i : Nat) (r : CtaBarrier.Record EvId), (X.barriers (e.1 / L.block))[i]? = some r ∧
      e ∈ r.refs := by
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt (thread_lt_of_get hX he)
  have hret : Returned X e := by simp [Returned, he, Kind.resume, hlt]
  have hmem : Need.node (fun x => ∃ i, ∃ r : CtaBarrier.Record EvId, ∃ y,
      (X.barriers (e.1 / L.block))[i]? = some r ∧ e ∈ r.refs ∧ x = .thread y ∧
      y.1 = warpLane L e.1 0 ∧ (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
        (X.barriers (e.1 / L.block))[j]? = some (CtaBarrier.Record.exit g y))) ∈
      Needs L X e := by
    simp only [Needs, he, KindNeeds, ctaBarNeeds]
    apply List.mem_append_left
    refine List.mem_map.mpr ⟨warpLane L e.1 0, List.mem_map.mpr ⟨0, ?_, rfl⟩, rfl⟩
    have h1 := Nat.mod_lt e.1 hb
    have h2 := Nat.div_mul_le_self (e.1 % L.block) 32
    simp only [List.mem_range, warpSize]
    omega
  obtain ⟨x, -, i, r, y, hi, her, -⟩ := hX.dependency.ready e hret _ hmem
  exact ⟨i, r, hi, her⟩

section Old
variable {c : Nat} {suffix : List (CtaBarrier.Record EvId)}

/-- A record of the extended history that holds a reference of an old record is an old
record. -/
theorem old_record_lt (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    {d : Nat} (hd : d < L.grid) {s : List (CtaBarrier.Record EvId)}
    (hs : (X.withCtaHistory c (X.barriers c ++ suffix)).barriers d = X.barriers d ++ s)
    {e : EvId} {i0 : Nat} {r0 : CtaBarrier.Record EvId} (hi0 : (X.barriers d)[i0]? = some r0)
    (he0 : e ∈ r0.refs) {i : Nat} {r : CtaBarrier.Record EvId}
    (hi : (X.barriers d ++ s)[i]? = some r) (he : e ∈ r.refs) : i < (X.barriers d).length := by
  by_contra hn
  have hnd := (hh.2 d hd).1
  rw [hs, List.flatMap_append, List.nodup_append] at hnd
  rw [List.getElem?_append_right (by omega)] at hi
  exact hnd.2.2 e (List.mem_flatMap.mpr ⟨r0, List.mem_of_getElem? hi0, he0⟩) e
    (List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hi, he⟩) rfl

/-- The warp need of lane `h` of a recorded arrival reads only the arrival's record and the
records before it, which are old. -/
theorem warpFill_old (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    {d : Nat} (hd : d < L.grid) {e : EvId} {i0 : Nat} {r0 : CtaBarrier.Record EvId}
    (hi0 : (X.barriers d)[i0]? = some r0) (he0 : e ∈ r0.refs) (h : Nat) (x : Ref) :
    (∃ i, ∃ r : CtaBarrier.Record EvId, ∃ y,
      ((X.withCtaHistory c (X.barriers c ++ suffix)).barriers d)[i]? = some r ∧ e ∈ r.refs ∧
      x = .thread y ∧ y.1 = h ∧ (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
        ((X.withCtaHistory c (X.barriers c ++ suffix)).barriers d)[j]? =
          some (CtaBarrier.Record.exit g y))) ↔
    (∃ i, ∃ r : CtaBarrier.Record EvId, ∃ y, (X.barriers d)[i]? = some r ∧ e ∈ r.refs ∧
      x = .thread y ∧ y.1 = h ∧ (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧
        (X.barriers d)[j]? = some (CtaBarrier.Record.exit g y))) := by
  obtain ⟨s, hs⟩ := withCtaHistory_append X c d suffix
  rw [hs]
  constructor
  · rintro ⟨i, r, y, hi, her, hx, hy, hor⟩
    have hil := old_record_lt hh hd hs hi0 he0 hi her
    rw [List.getElem?_append_left hil] at hi
    refine ⟨i, r, y, hi, her, hx, hy, ?_⟩
    rcases hor with hyr | ⟨j, g, hj, hjr⟩
    · exact .inl hyr
    · rw [List.getElem?_append_left (by omega)] at hjr
      exact .inr ⟨j, g, hj, hjr⟩
  · rintro ⟨i, r, y, hi, her, hx, hy, hor⟩
    have hil : i < (X.barriers d).length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨i, r, y, by rw [List.getElem?_append_left hil]; exact hi, her, hx, hy, ?_⟩
    rcases hor with hyr | ⟨j, g, hj, hjr⟩
    · exact .inl hyr
    · exact .inr ⟨j, g, hj, by rw [List.getElem?_append_left (by omega)]; exact hjr⟩

/-- A reference counted by the release that a returned `bar.sync` waits for is counted in `X`:
its generation was released in the old history, so the completing record and every counted
record are old. -/
theorem counted_old (hX : Consistent L K A mem0 X)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    {e y : EvId} {key0 : Nat} (hk0 : CtaBarK L X e key0)
    (hd0 : CtaBarDone L X (e.1 / L.block) key0)
    (hc : CtaBarCounted L (X.withCtaHistory c (X.barriers c ++ suffix)) e y) :
    CtaBarCounted L X e y ∧ y ∈ (X.barriers (e.1 / L.block)).flatMap CtaBarrier.Record.refs := by
  obtain ⟨key, ic, hkY, hcomp, i, r, hi, hyr, hle, hshape⟩ := hc
  have hkey : key = key0 :=
    CtaBarK.key_unique hh hkY (hk0.mono (X.le_withCtaHistory c ⟨suffix, rfl⟩))
  subst hkey
  have hd : e.1 / L.block < L.grid :=
    (Nat.div_lt_iff_lt_mul (NamedBar.block_pos_of_thread_lt hk0.1)).mpr hk0.1
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 _ hd
  obtain ⟨s, hs⟩ := withCtaHistory_append X c (e.1 / L.block) suffix
  rw [hs] at hcomp hi hshape
  rcases CtaBarrier.CompletesAt.append_cases hlast hcomp with hcX | hge
  · have hic : ic < (X.barriers (e.1 / L.block)).length := by
      obtain ⟨_, _, _, hic, -⟩ := hcX
      exact (List.getElem?_eq_some_iff.mp hic).1
    have hil : i < (X.barriers (e.1 / L.block)).length := by omega
    rw [List.getElem?_append_left hil] at hi
    refine ⟨⟨key, ic, hk0, hcX, i, r, hi, hyr, hle, ?_⟩,
      List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hi, hyr⟩⟩
    rcases hshape with ⟨w, count, lanes, st, hr, hat, hgen⟩ | hex
    · refine .inl ⟨w, count, lanes, st, hr, ?_, hgen⟩
      unfold CtaBarrier.At at hat ⊢
      rwa [List.take_append_of_le_length hil.le] at hat
    · exact .inr hex
  · exact absurd (CtaBarrier.released_generation_lt hlast hd0) (by omega)

/-- **The node needs of an old event are those of `X`**, when the event, if it is a CTA barrier
arrival, has returned. -/
theorem needs_node_old (hX : Consistent L K A mem0 X)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix))) {e : EvId}
    (hret : ∀ pc id cnt m, X.get e = some ⟨pc, .bar id cnt m⟩ → e.2 + 1 < (X.tr e.1).length)
    {fills : Ref → Prop}
    (hn : Need.node fills ∈ Needs L (X.withCtaHistory c (X.barriers c ++ suffix)) e) :
    ∃ fills', Need.node fills' ∈ Needs L X e ∧ ∀ x, fills x ↔ fills' x := by
  have hget : (X.withCtaHistory c (X.barriers c ++ suffix)).get e = X.get e := rfl
  unfold Needs at hn ⊢
  rw [hget] at hn
  cases hev : X.get e with
  | none => rw [hev] at hn; cases hn
  | some ev =>
    rw [hev] at hn
    obtain ⟨pc, k⟩ := ev
    simp only at hn ⊢
    cases k with
    | bar id cnt m =>
      have hlt := hret pc id cnt m hev
      have hd : e.1 / L.block < L.grid :=
        (Nat.div_lt_iff_lt_mul (NamedBar.block_pos_of_thread_lt (thread_lt_of_get hX hev))).mpr
          (thread_lt_of_get hX hev)
      obtain ⟨i0, r0, hi0, he0⟩ := recorded_of_returned hX hev hlt
      simp only [KindNeeds, ctaBarNeeds, List.mem_append] at hn ⊢
      rcases hn with hw | hrest
      · obtain ⟨h, hhm, hfl⟩ := List.mem_map.mp hw
        cases hfl
        refine ⟨_, .inl (List.mem_map.mpr ⟨h, hhm, rfl⟩), fun x => ?_⟩
        exact warpFill_old hh hd hi0 he0 h x
      · cases m with
        | arrive => cases hrest
        | sync =>
          rcases List.mem_cons.mp hrest with hcond | hcount
          · cases hcond
          · obtain ⟨y, -, hy⟩ := List.mem_flatMap.mp hcount
            obtain ⟨hcy, hfl⟩ := mem_needsIf_node.mp hy
            cases List.mem_singleton.mp hfl
            obtain ⟨key0, hk0, hd0⟩ := ctaBarDone_of_returned hX hev hlt
            obtain ⟨hcX, hyX⟩ := counted_old hX hh hk0 hd0 hcy
            refine ⟨_, .inr (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
              ⟨y, hyX, mem_needsIf_node.mpr ⟨hcX, List.mem_singleton_self _⟩⟩)),
              fun _ => Iff.rfl⟩
    | tc t => exact ⟨fills, by cases t <;> exact hn, fun _ => Iff.rfl⟩
    | _ => exact ⟨fills, hn, fun _ => Iff.rfl⟩

/-- A witness of an old event in the extended execution is one of `X`, when the event, if it is
a CTA barrier arrival, has returned. -/
theorem witness_old (hX : Consistent L K A mem0 X)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix))) {x : Ref} {e : EvId}
    (hret : ∀ pc id cnt m, X.get e = some ⟨pc, .bar id cnt m⟩ → e.2 + 1 < (X.tr e.1).length)
    (hw : Witness L (X.withCtaHistory c (X.barriers c ++ suffix)) x e) : Witness L X x e := by
  obtain ⟨fills, hn, hx, hf⟩ := hw
  obtain ⟨fills', hn', hiff⟩ := needs_node_old hX hh hret hn
  exact ⟨fills', hn', hx, (hiff x).mp hf⟩

/-- **Readiness survives appending records**: a returned event's needs are those of `X`, and the
release a `bar.sync` waits for stays released. -/
theorem ready_append (hX : Consistent L K A mem0 X)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix))) (e : EvId)
    (hr : Returned (X.withCtaHistory c (X.barriers c ++ suffix)) e) :
    Ready L (X.withCtaHistory c (X.barriers c ++ suffix)) e := by
  have hrX : Returned X e := hr
  have hready := hX.dependency.ready e hrX
  have hret : ∀ pc id cnt m, X.get e = some ⟨pc, .bar id cnt m⟩ →
      e.2 + 1 < (X.tr e.1).length := by
    intro pc id cnt m hev
    simpa [Returned, hev, Kind.resume] using hrX
  intro n hn
  cases n with
  | node fills =>
    obtain ⟨fills', hn', hiff⟩ := needs_node_old hX hh hret hn
    obtain ⟨x, hx, hf⟩ := hready _ hn'
    exact ⟨x, hx, (hiff x).mpr hf⟩
  | cond P =>
    have hget : (X.withCtaHistory c (X.barriers c ++ suffix)).get e = X.get e := rfl
    unfold Needs at hn
    rw [hget] at hn
    cases hev : X.get e with
    | none => rw [hev] at hn; cases hn
    | some ev =>
      rw [hev] at hn
      obtain ⟨pc, k⟩ := ev
      have hcondX : ∀ Q, Need.cond Q ∈ KindNeeds L X k e → Q := by
        intro Q hQ
        have := hready (.cond Q) (by unfold Needs; rw [hev]; exact hQ)
        exact this
      simp only at hn
      cases k with
      | bar id cnt m =>
        simp only [KindNeeds, ctaBarNeeds, List.mem_append] at hn
        rcases hn with hw | hrest
        · obtain ⟨h, -, hfl⟩ := List.mem_map.mp hw
          cases hfl
        · cases m with
          | arrive => cases hrest
          | sync =>
            rcases List.mem_cons.mp hrest with hcond | hcount
            · cases hcond
              obtain ⟨key, hk, hd⟩ := ctaBarDone_of_returned hX hev (hret pc id cnt .sync hev)
              have hle := X.le_withCtaHistory c ⟨suffix, rfl⟩
              exact ⟨key, hk.mono hle, hd.mono hle⟩
            · obtain ⟨y, -, hy⟩ := List.mem_flatMap.mp hcount
              unfold needsIf at hy
              split_ifs at hy
              · cases List.mem_singleton.mp hy
              · cases hy
      | tc t => exact hcondX P (by cases t <;> exact hn)
      | _ => exact hcondX P hn

/-- **The dependency steps between old nodes are those of `X`**, when the node set holds the
return nodes of the CTA barrier arrivals that have not returned. -/
theorem dep_append (hX : Consistent L K A mem0 X)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    (S : Ref × Bool → Prop)
    (hS : ∀ j pc id cnt m, X.get j = some ⟨pc, .bar id cnt m⟩ →
      j.2 + 1 = (X.tr j.1).length → S (.thread j, true))
    (u v : Ref × Bool) (_hu : ¬ S u) (hv : ¬ S v)
    (h : DepStep L K (X.withCtaHistory c (X.barriers c ++ suffix)) u v) :
    Relation.TransGen (DepStep L K X) u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  rcases h with h | h | ⟨hb, hb', j, rfl, hw⟩ | h
  · exact .single (.inl h)
  · exact .single (.inr (.inl h))
  · subst hb'
    refine .single (.inr (.inr (.inl ⟨hb, rfl, j, rfl, witness_old hX hh ?_ hw⟩)))
    intro pc id cnt m hev
    have hl : j.2 < (X.tr j.1).length := len_of_get hev
    by_contra hn
    exact hv (hS j pc id cnt m hev (by omega))
  · exact .single (.inr (.inr (.inr h)))

end Old

variable [hK : Fact K.NoBarArrive]

/-- Facts about the appended arrivals: their events are present barrier arrivals of the
CTA, and none of them is already recorded in `X`. -/
theorem suffix_ref_facts {c : Nat} {suffix : List (CtaBarrier.Record EvId)} (hc : c < L.grid)
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    {r : CtaBarrier.Record EvId} (hr : r ∈ suffix) {e : EvId} (he : e ∈ r.refs) :
    e.1 / L.block = c ∧ (∃ id count pc, X.IsBarArrival e id count pc) ∧
      e ∉ (X.barriers c).flatMap CtaBarrier.Record.refs := by
  have hrY : r ∈ (X.withCtaHistory c (X.barriers c ++ suffix)).barriers c := by
    rw [withCtaHistory_barriers_self]
    exact List.mem_append_right _ hr
  have hsrc := (hh.2 c hc).2.1 r hrY
  refine ⟨hsrc.ref_cta he, ?_, ?_⟩
  · obtain ⟨id, warp, count, lanes, rfl⟩ := hsuf r hr
    simp only [CtaBarrier.Record.refs, List.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    obtain ⟨-, -, pc, hpc⟩ := hsrc p hp
    exact ⟨id, count, pc, hpc⟩
  · have hnd : ((X.barriers c ++ suffix).flatMap CtaBarrier.Record.refs).Nodup := by
      have h := (hh.2 c hc).1
      rw [withCtaHistory_barriers_self] at h
      exact h
    rw [List.flatMap_append, List.nodup_append] at hnd
    intro hmem
    exact hnd.2.2 e hmem e (List.mem_flatMap.mpr ⟨r, hr, he⟩) rfl

/-- Every appended arrival is terminal. -/
theorem suffix_terminal (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    {r : CtaBarrier.Record EvId} (hr : r ∈ suffix) {e : EvId} (he : e ∈ r.refs) :
    TerminalBar X e := by
  obtain ⟨hec, ⟨id, count, pc, hI⟩, hfresh⟩ := suffix_ref_facts hc hsuf hh hr he
  replace hI := hX.isBarrier_of_arrival hK.out hI
  refine ⟨⟨id, count, pc, hI⟩, ?_⟩
  by_contra hne
  have hlt : e.2 + 1 < (X.tr e.1).length := by
    have h1 : e.2 < (X.tr e.1).length := len_of_get hI
    omega
  obtain ⟨i, r', hi, her'⟩ := recorded_of_returned hX hI hlt
  rw [hec] at hi
  exact hfresh (List.mem_flatMap.mpr ⟨r', List.mem_of_getElem? hi, her'⟩)

/-- An appended arrival's key generation is still open in the history of `X`. -/
theorem suffix_key_not_done {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    {s : CtaBarrier.State} (hs : CtaBarrier.run L.block {} (X.barriers c) = .ok s)
    {r : CtaBarrier.Record EvId} (hr : r ∈ suffix) {e : EvId} (he : e ∈ r.refs) {key : Nat}
    (hk : CtaBarArrivalK L (X.withCtaHistory c (X.barriers c ++ suffix)) e key) :
    ¬ CtaBarDone L X c key := by
  obtain ⟨hec, -, hfresh⟩ := suffix_ref_facts hc hsuf hh hr he
  rcases ctaBarArrivalK_append_cases hs hec hk with h | h
  · obtain ⟨-, -, hg⟩ := h
    obtain ⟨r', hr', her'⟩ := mem_refs_of_generationOf hg
    rw [hec] at hr'
    exact absurd (List.mem_flatMap.mpr ⟨r', hr', her'⟩) hfresh
  · exact not_released_of_ge hs h

omit hK in
/-- A waiting edge out of an appended issue node stays in the suffix, in record order, or lands
on the return node of a terminal arrival. -/
theorem ctaWaits_forward (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    {e f : EvId} {b' : Bool} (he : e ∈ suffix.flatMap CtaBarrier.Record.refs)
    (hw : CtaBarWaits L (X.withCtaHistory c (X.barriers c ++ suffix)) e f false b') :
    (b' = false ∧ f ∈ suffix.flatMap CtaBarrier.Record.refs ∧
        ((X.barriers c ++ suffix).flatMap CtaBarrier.Record.refs).idxOf e <
          ((X.barriers c ++ suffix).flatMap CtaBarrier.Record.refs).idxOf f) ∨
      (b' = true ∧ TerminalBar X f) := by
  obtain ⟨r0, hr0, her0⟩ := List.mem_flatMap.mp he
  obtain ⟨-, -, s, hs⟩ := hX.ctaBar.2 c hc
  have hnd : ((X.barriers c ++ suffix).flatMap CtaBarrier.Record.refs).Nodup := by
    have h := (hh.2 c hc).1
    rw [withCtaHistory_barriers_self] at h
    exact h
  have hec : e.1 / L.block = c := (suffix_ref_facts hc hsuf hh hr0 her0).1
  have hfresh := (suffix_ref_facts hc hsuf hh hr0 her0).2.2
  have hpre : X.barriers c <+: X.barriers c ++ suffix := ⟨suffix, rfl⟩
  obtain ⟨-, -, hcase⟩ := hw
  rcases hcase with ⟨hb, hb', d, i', j', r, q, hr, hq, hij, her, hfq⟩ |
    ⟨hb, hb', hscope, key, hke, hkf⟩ | ⟨hb, hb', key, i', r, hkf, hr, her, hcomp⟩
  · -- consecutive records: the source record lies in the suffix, so does the target
    have hdc : d = c := (CtaBarHistoryOk.ref_cta hh (List.mem_of_getElem? hr) her).symm.trans hec
    rw [hdc, withCtaHistory_barriers_self] at hr hq
    have hge_i : (X.barriers c).length ≤ i' := by
      by_contra hlt
      have hl : i' < (X.barriers c).length := by omega
      rw [List.getElem?_append_left hl] at hr
      exact hfresh (List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hr, her⟩)
    have hge_j : (X.barriers c).length ≤ j' := by omega
    have hqs : q ∈ suffix :=
      List.mem_of_getElem? (by rwa [List.getElem?_append_right hge_j] at hq)
    exact .inl ⟨hb', List.mem_flatMap.mpr ⟨q, hqs, hfq⟩,
      CtaBarrier.refs_index_lt hnd hr hq hij her hfq⟩
  · -- two arrivals with one resource key: the key is open unless both are old
    have hd : ¬ CtaBarDone L X c key := suffix_key_not_done hc hsuf hh hs hr0 her0 hke
    have hjc : f.1 / L.block = c := by rw [← hscope.2.2, hec]
    exact .inr ⟨hb', terminal_of_not_done hX hpre hh hkf hjc hd⟩
  · -- a completion: the completing record lies in the suffix, so the target is terminal
    have hdc : f.1 / L.block = c :=
      (CtaBarHistoryOk.ref_cta hh (List.mem_of_getElem? hr) her).symm.trans hec
    rw [hdc, withCtaHistory_barriers_self] at hr hcomp
    have hge_i : (X.barriers c).length ≤ i' := by
      by_contra hlt
      have hl : i' < (X.barriers c).length := by omega
      rw [List.getElem?_append_left hl] at hr
      exact hfresh (List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hr, her⟩)
    have hnd' : ¬ CtaBarDone L X c key := suffix_completes_not_done hs hcomp hge_i
    exact .inr ⟨hb', terminal_of_not_done hX hpre hh hkf hdc hnd'⟩


/-- The nodes added by appending a checked suffix of arrivals: the suffix's issue nodes and
the return nodes of terminal arrivals. -/
def SuffixNode (X : Execution) (suffix : List (CtaBarrier.Record EvId)) (p : AsyncCopy.Ref × Bool) :
    Prop :=
  (∃ e, p = (.thread e, true) ∧ TerminalBar X e) ∨
    (∃ e, p = (.thread e, false) ∧ e ∈ suffix.flatMap CtaBarrier.Record.refs)

/-- Appending a checked suffix of arrivals extends the execution by the suffix nodes: no waiting
dependency leaves them, the rank orders issue nodes by record position and puts every return
node above them, and outside them every relation is one of `X`. -/
theorem suffix_sinkFrame (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix))) :
    SinkFrame L K A X (X.withCtaHistory c (X.barriers c ++ suffix)) (SuffixNode X suffix) := by
  have hYE : EffectValidity L (X.withCtaHistory c (X.barriers c ++ suffix)) :=
    effectValidity_withCtaHistory_legacy hX
  refine ctaHistory_append_prim hX hh _ (fun j hj => .inr ⟨j, rfl, hj⟩)
    ⟨rankOf ((X.barriers c ++ suffix).flatMap CtaBarrier.Record.refs), ?_⟩ ?_
    (dep_append hX hh _ ?_)
  · intro u v hw hu
    obtain ⟨ue, ub⟩ := u
    obtain ⟨ve, vb⟩ := v
    rcases hu with ⟨e, hue, hT⟩ | ⟨e, hue, he⟩
    · -- a return node: it has no successor
      simp only [Prod.mk.injEq] at hue
      obtain ⟨rfl, rfl⟩ := hue
      obtain ⟨id, count, pc, hI⟩ := hT.1
      have hI' : (X.withCtaHistory c (X.barriers c ++ suffix)).IsBarrier e id count pc := hI
      have ht' : e.2 + 1 = ((X.withCtaHistory c (X.barriers c ++ suffix)).tr e.1).length := hT.2
      have h0 := (terminal_barrier_waits_cases hYE hh hX.cluster hX.tmemPair hI' ht' hw).1
      exact absurd h0 (by decide)
    · -- an issue node of the suffix
      simp only [Prod.mk.injEq] at hue
      obtain ⟨rfl, rfl⟩ := hue
      obtain ⟨r, hr, her⟩ := List.mem_flatMap.mp he
      have hT := suffix_terminal hX hc hsuf hh hr her
      obtain ⟨hec, -, hfresh⟩ := suffix_ref_facts hc hsuf hh hr her
      obtain ⟨id, count, pc, hI⟩ := hT.1
      have hI' : (X.withCtaHistory c (X.barriers c ++ suffix)).IsBarrier e id count pc := hI
      have ht' : e.2 + 1 = ((X.withCtaHistory c (X.barriers c ++ suffix)).tr e.1).length := hT.2
      have hmem : e ∈ (X.barriers c ++ suffix).flatMap CtaBarrier.Record.refs :=
        List.mem_flatMap.mpr ⟨r, List.mem_append_right _ hr, her⟩
      have hlen := List.idxOf_lt_length_iff.mpr hmem
      rcases (terminal_barrier_waits_cases hYE hh hX.cluster hX.tmemPair hI' ht' hw).2 with
        h | ⟨f, b', h, hcw | ⟨hb', d, i, q, hq, heq, hfq⟩⟩
      · -- the return node of the same arrival
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨Or.inl ⟨e, rfl, hT⟩, ?_⟩
        simp only [rankOf]
        omega
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases ctaWaits_forward hX hc hsuf hh he hcw with ⟨hb', hfS, hidx⟩ | ⟨hb', hfT⟩
        · subst hb'
          refine ⟨Or.inr ⟨f, rfl, hfS⟩, ?_⟩
          simp only [rankOf]
          exact hidx
        · subst hb'
          refine ⟨Or.inl ⟨f, rfl, hfT⟩, ?_⟩
          simp only [rankOf]
          omega
      · -- a lane of the same record: the record is appended, so the lane is terminal
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hb'
        have hdc : d = c := (hh.ref_cta (List.mem_of_getElem? hq) heq).symm.trans hec
        subst hdc
        rw [withCtaHistory_barriers_self] at hq
        have hge : (X.barriers d).length ≤ i := by
          by_contra hlt
          rw [List.getElem?_append_left (by omega)] at hq
          exact hfresh (List.mem_flatMap.mpr ⟨q, List.mem_of_getElem? hq, heq⟩)
        rw [List.getElem?_append_right hge] at hq
        have hqs := List.mem_of_getElem? hq
        refine ⟨Or.inl ⟨f, rfl, suffix_terminal hX hc hsuf hh hqs hfq⟩, ?_⟩
        simp only [rankOf]
        omega
  · rintro m i p y hb (⟨e, he, -⟩ | ⟨e, he, hm⟩)
    · cases he
    · cases he
      obtain ⟨r, hr, her⟩ := List.mem_flatMap.mp hm
      obtain ⟨-, ⟨id, count, pc, mode, hI⟩, -⟩ := suffix_ref_facts hc hsuf hh hr her
      exact (sync_no_async_before hX.tma hI (.inl ⟨_, _, _, rfl⟩) m p y hb).elim
  · intro j pc id cnt m hev hlast
    cases m with
    | sync => exact .inl ⟨j, rfl, ⟨id, cnt, pc, hev⟩, hlast⟩
    | arrive => exact (hX.noBarArrive hK.out j pc id cnt hev).elim

omit hK in
/-- The obligations of an extension that only appends records to one CTA's history: every field
other than the CTA history reads parts of the execution that stay unchanged, and Fence-SC is
constrained against a base causality that is unchanged. -/
theorem withCtaHistory_obligations (hX : Consistent L K A mem0 X) {c : Nat}
    {suffix : List (CtaBarrier.Record EvId)} (hp : X.barriers c <+: X.barriers c ++ suffix)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    (hbo : ∀ e f, baseCausality L (X.withCtaHistory c (X.barriers c ++ suffix)) e f ↔
      baseCausality L X e f) :
    ExtensionObligations L A (X.withCtaHistory c (X.barriers c ++ suffix)) where
  ctaBar := hh
  cluster := hX.cluster
  elect := hX.elect
  vote := hX.vote
  warpValue := hX.warpValue
  warpBar := hX.warpBar
  matrix := hX.matrix
  clc := hX.clc
  tensor := hX.tensor
  store := hX.store
  atomic := ⟨fun p q l n k hp hq hne hs hk =>
      hX.atomic.unique p q l n k hp hq hne ((rmwStrong_congr rfl rfl).mp hs) hk,
    fun p hc => hX.atomic.acyclic p (Relation.TransGen.mono (fun _ _ hab => by
      obtain ⟨l, n, ha, hb, hs, rest⟩ := hab
      exact ⟨l, n, ha, hb, (rmwStrong_congr rfl rfl).mp hs, rest⟩) _ _ hc)⟩
  fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic,
    fun e f hs hc => hX.fenceSc.causal e f hs ((hbo e f).mp hc)⟩
  tmemPair := hX.tmemPair
  tmemPairResult := hX.tmemPairResult
  tmemPairCompletion := hX.tmemPairCompletion
  tcCommit := hX.tcCommit
  mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl
  tcRead := readOk_withCtaHistory hX hp hbo
  reduce := hX.reduce.of_tensorStores rfl fun _ _ _ _ hY _ _ => ⟨hY, rfl⟩

/-- Appending a checked suffix of arrivals to one CTA's history keeps the execution consistent.
Only the CTA barrier relations and the CTA resource records change, and those changes are classified
above; memory order is unchanged, since a resource phase passed by a waiting arrival cannot be
joined by a later one. -/
theorem suffix_consistent (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.withCtaHistory c (X.barriers c ++ suffix))) :
    Consistent L K A mem0 (X.withCtaHistory c (X.barriers c ++ suffix)) := by
  have hp : X.barriers c <+: X.barriers c ++ suffix := ⟨suffix, rfl⟩
  have hle : X.le (X.withCtaHistory c (X.barriers c ++ suffix)) :=
    X.le_withCtaHistory c hp
  have hbo := baseCausality_withCtaHistory_iff hX hp hh
  have horder := (suffix_sinkFrame hX hc hsuf hh).orderOk hX.orderOk
  apply consistent_preserving_extension hX hle
  · exact hX.thr
  · exact hX.outside
  · intro e a bs he; exact he
  · intro e a bs he; exact he
  · intro e a bs he; exact he
  · intros; rfl
  · intro l e f _; exact modelCausality_withCtaHistory hbo
  · exact ready_append hX hh
  · exact hX.shfl
  · exact horder
  · exact hasm
  · exact hX.tma
  · rfl
  · exact withCtaHistory_obligations hX hp hh hbo

/-- Appending a checked suffix of arrival records for one CTA's current generation: the extended
execution is consistent, extends the old one at the same size, and a maximal execution stays
maximal. -/
theorem release_append (hmax : Maximal L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.withCtaHistory c (X.barriers c ++ suffix))) :
    Consistent L K A mem0 (X.withCtaHistory c (X.barriers c ++ suffix)) ∧
      X.le (X.withCtaHistory c (X.barriers c ++ suffix)) ∧
      (X.withCtaHistory c (X.barriers c ++ suffix)).size L = X.size L ∧
      Maximal L K A mem0 (X.withCtaHistory c (X.barriers c ++ suffix)) := by
  have hY := suffix_consistent hmax.1 hc hsuf hh hasm
  have hle : X.le (X.withCtaHistory c (X.barriers c ++ suffix)) :=
    X.le_withCtaHistory c ⟨suffix, rfl⟩
  have hsz : (X.withCtaHistory c (X.barriers c ++ suffix)).size L = X.size L := rfl
  refine ⟨hY, hle, hsz, hY, fun Z hZ hYZ => ?_⟩
  have h1 := hmax.2 Z hZ (Execution.le_trans hle hYZ)
  omega


/-! ## Arrival counts of a named resource

The named-barrier ledger (`NamedBar.Protocol`) describes one resource: its participant warps `p`
(`n` of them, each passing a thread-count operand `count` that decodes to `n` warps), and only
arrivals of those warps on this resource. Its replay gives, for each participant warp, the number
of arrivals equal to the generation plus one exactly when the warp is in the arrived set of the
current generation. -/

/-- A single record raises a resource generation by at most one. -/
theorem perform_generation_le_succ {α : Type} {block : Nat} {s t : CtaBarrier.State}
    {r : CtaBarrier.Record α} (h : r.perform block s = .ok t) (id : Nat) :
    (t.slots id).generation ≤ (s.slots id).generation + 1 := by
  cases r with
  | exit g e =>
    by_cases hg : g < block ∧ g ∉ s.exited
    · simp [CtaBarrier.Record.perform, CtaBarrier.exitThread, hg, pure, Except.pure] at h
      cases h
      have hh := CtaBarrier.settle_generation block (insert g s.exited) (s.slots id)
      change (CtaBarrier.settle block (insert g s.exited) (s.slots id)).generation ≤ _
      omega
    · simp [CtaBarrier.Record.perform, CtaBarrier.exitThread, hg, bind, Except.bind,
        pure, Except.pure, throw] at h
  | arrival slot warp count lanes =>
    simp only [CtaBarrier.Record.perform] at h
    split_ifs at h
    obtain ⟨n, -, -, hslots⟩ := CtaBarrier.arrive_shape h
    rw [hslots]
    split_ifs with heq
    · subst heq
      have key : ∀ x : CtaBarrier.Slot,
          (CtaBarrier.settle block s.exited x).generation ≤ x.generation + 1 := by
        intro x
        have := CtaBarrier.settle_generation block s.exited x
        omega
      exact key _
    · omega

/-- A later generation of a checked history was started by a completion of every earlier
generation: a generation advance is a released generation. -/
theorem released_of_generation_lt {α : Type} {block id phase : Nat}
    {h : List (CtaBarrier.Record α)} {t : CtaBarrier.State}
    (hr : CtaBarrier.run block {} h = .ok t) (hlt : phase < (t.slots id).generation) :
    CtaBarrier.Released block h id phase := by
  induction h using List.reverseRecOn generalizing t with
  | nil =>
    simp only [CtaBarrier.run, Except.ok.injEq] at hr
    subst hr
    simp at hlt
  | @append_singleton xs r ih =>
    obtain ⟨u, hu⟩ := CtaBarrier.run_prefix hr
    have hf : r.perform block u = .ok t := by
      rw [CtaBarrier.run_append, hu] at hr
      cases hf : r.perform block u with
      | error err => simp [CtaBarrier.run, hf, Except.bind] at hr
      | ok v => simpa only [CtaBarrier.run, hf, Except.bind, Except.ok.injEq, throw, throwThe,
          MonadExceptOf.throw] using hr
    have hle := perform_generation_le_succ hf id
    by_cases hu' : phase < (u.slots id).generation
    · exact CtaBarrier.Released.append (ih hu hu')
    · have hph : (u.slots id).generation = phase := by omega
      refine ⟨xs.length, r, u, t, ?_, ?_, hf, hph, by omega⟩
      · simp
      · unfold CtaBarrier.At
        rw [List.take_left' (by simp)]
        exact hu

end

end PTX.Step.CtaBar
