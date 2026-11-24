-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.CtaBarrier.CtaBarrierHistory

@[expose] public section

namespace PTX

variable {L : Launch} {X Y : Execution}

/-- Source-event provenance survives extension of the actual thread traces. -/
theorem CtaBarSources.mono {c : Nat} {r : CtaBarrier.Record EvId}
    (hr : CtaBarSources L X c r) (h : X.le Y) : CtaBarSources L Y c r := by
  cases r with
  | exit g e =>
    obtain ⟨hg, he, pc, hp⟩ := hr
    exact ⟨hg, he, pc, Execution.le_get h hp⟩
  | arrival id w count lanes =>
    intro p hp
    obtain ⟨hg, he, pc, mode, hb⟩ := hr p hp
    exact ⟨hg, he, pc, mode, Execution.le_get h hb⟩

/-- An existing arrival keeps its actual generation when the execution grows. -/
theorem CtaBarK.mono {e : EvId} {key : Nat} (hk : CtaBarK L X e key)
    (h : X.le Y) : CtaBarK L Y e key := by
  obtain ⟨hg, ⟨count, pc, hp⟩, hi⟩ := hk
  refine ⟨hg, ⟨count, pc, Execution.le_get h hp⟩, ?_⟩
  obtain ⟨suffix, hs⟩ := h.2.2.2.2.1 (e.1 / L.block)
  rw [← hs]
  exact hi.append

theorem CtaBarK.arrival {e : EvId} {k : Nat} (h : CtaBarK L X e k) : CtaBarArrivalK L X e k := by
  obtain ⟨h1, ⟨c, pc, h2⟩, h3⟩ := h
  exact ⟨h1, ⟨c, pc, _, h2⟩, h3⟩

/-- An existing arrival of either form keeps its actual generation when the execution grows. -/
theorem CtaBarArrivalK.mono {e : EvId} {key : Nat} (hk : CtaBarArrivalK L X e key)
    (h : X.le Y) : CtaBarArrivalK L Y e key := by
  obtain ⟨hg, ⟨count, pc, mode, hp⟩, hi⟩ := hk
  refine ⟨hg, ⟨count, pc, mode, Execution.le_get h hp⟩, ?_⟩
  obtain ⟨suffix, hs⟩ := h.2.2.2.2.1 (e.1 / L.block)
  rw [← hs]
  exact hi.append

/-- A later phase cannot revoke the completion of an earlier phase. -/
theorem CtaBarDone.mono {c key : Nat} (hk : CtaBarDone L X c key)
    (h : X.le Y) : CtaBarDone L Y c key := by
  obtain ⟨suffix, hs⟩ := h.2.2.2.2.1 c
  unfold CtaBarDone
  rw [← hs]
  exact hk.append

theorem CtaBarSync.mono {e f : EvId} (hs : CtaBarSync L X e f)
    (h : X.le Y) : CtaBarSync L Y e f := by
  obtain ⟨hc, key, i, j, hi, hj, he, hf, hlen⟩ := hs
  exact ⟨hc, key, i, j, hi.mono h, hj.mono h, he, hf,
    lt_of_lt_of_le hlen (h.1 f.1).length_le⟩

/-- Keeping the checked resource histories while adding thread events preserves
all their source checks. This is used by non-barrier extension proofs. -/
theorem CtaBarHistoryOk.preserving (hx : CtaBarHistoryOk L X) (h : X.le Y)
    (hb : Y.barriers = X.barriers) : CtaBarHistoryOk L Y := by
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [hb]
    exact hx.1 c hc
  · intro c hc
    obtain ⟨hn, hs, ht⟩ := hx.2 c hc
    rw [hb]
    exact ⟨hn, fun r hr => (hs r hr).mono h, ht⟩

theorem CtaBarHistoryOk.empty (L : Launch) : CtaBarHistoryOk L Execution.empty := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro c hc
  exact ⟨by simp [Execution.empty], by simp [Execution.empty], ⟨{}, rfl⟩⟩

theorem CtaBarK.not_empty (L : Launch) (e : EvId) (key : Nat) :
    ¬ CtaBarK L Execution.empty e key := by
  rintro ⟨_, ⟨count, pc, hp⟩, _⟩
  simp [Execution.IsBarrier, Execution.get, Execution.empty] at hp

/-- Every event referenced by a checked resource history is a real source event. -/
theorem CtaBarHistoryOk.ref_present {L : Launch} {X : Execution}
    (h : CtaBarHistoryOk L X) {c : Nat} {record : CtaBarrier.Record EvId} {e : EvId}
    (hr : record ∈ X.barriers c) (he : e ∈ record.refs) : ∃ ev, X.get e = some ev := by
  have hc : c < L.grid := by
    by_contra hn
    rw [h.1 c (by omega)] at hr
    cases hr
  have hs := (h.2 c hc).2.1 record hr
  cases record with
  | exit g f =>
    simp only [CtaBarrier.Record.refs,List.mem_singleton] at he
    subst f
    obtain ⟨_,_,pc,hp⟩ := hs
    exact ⟨_,hp⟩
  | arrival id warp count lanes =>
    simp only [CtaBarrier.Record.refs,List.mem_map] at he
    obtain ⟨p,hp,rfl⟩ := he
    obtain ⟨_,_,pc,_,hp⟩ := hs p hp
    exact ⟨_,hp⟩

/-- Every event referenced by a checked resource history is a barrier arrival or an exit. -/
theorem CtaBarHistoryOk.ref_not_access {L : Launch} {X : Execution}
    (h : CtaBarHistoryOk L X) {c : Nat} {record : CtaBarrier.Record EvId} {e : EvId}
    (hr : record ∈ X.barriers c) (he : e ∈ record.refs) : (X.get e).bind Event.acc = none := by
  have hc : c < L.grid := by
    by_contra hn
    rw [h.1 c (by omega)] at hr
    cases hr
  have hs := (h.2 c hc).2.1 record hr
  cases record with
  | exit g f =>
    simp only [CtaBarrier.Record.refs,List.mem_singleton] at he
    subst f
    obtain ⟨_,_,pc,hp⟩ := hs
    simp [hp, Event.acc]
  | arrival id warp count lanes =>
    simp only [CtaBarrier.Record.refs,List.mem_map] at he
    obtain ⟨p,hp,rfl⟩ := he
    obtain ⟨_,_,pc,_,hp⟩ := hs p hp
    simp [hp, Event.acc]

theorem CtaBarHistoryOk.generation_present {L : Launch} {X : Execution}
    (h : CtaBarHistoryOk L X) {c : Nat} {e : EvId} {id generation : Nat}
    (hg : CtaBarrier.GenerationOf L.block (X.barriers c) e id generation) :
    ∃ ev, X.get e = some ev := by
  obtain ⟨i,st,warp,count,lanes,g,hi,_,he,_⟩ := hg
  apply h.ref_present (List.mem_of_getElem? hi)
  exact List.mem_map.mpr ⟨(g,e),he,rfl⟩

theorem CtaBarWaits.mono {e f : EvId} {b b' : Bool}
    (hw : CtaBarWaits L X e f b b') (hle : X.le Y) : CtaBarWaits L Y e f b b' := by
  obtain ⟨⟨ev,he⟩,⟨fv,hf⟩,hh⟩ := hw
  refine ⟨⟨ev,Execution.le_get hle he⟩,⟨fv,Execution.le_get hle hf⟩,?_⟩
  rcases hh with ⟨hb,hb',c,i,j,r,q,hr,hq,hij,her,hfq⟩ |
    ⟨hb,hb',hscope,key,hke,hkf⟩ | ⟨hb,hb',key,i,r,hkf,hr,her,hcomp⟩
  · obtain ⟨suffix,hs⟩ := hle.2.2.2.2.1 c
    refine .inl ⟨hb,hb',c,i,j,r,q,?_,?_,hij,her,hfq⟩
    · rw [←hs,List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).1]; exact hr
    · rw [←hs,List.getElem?_append_left (List.getElem?_eq_some_iff.mp hq).1]; exact hq
  · exact .inr (.inl ⟨hb,hb',hscope,key,hke.mono hle,hkf.mono hle⟩)
  · obtain ⟨suffix,hs⟩ := hle.2.2.2.2.1 (f.1/L.block)
    refine .inr (.inr ⟨hb,hb',key,i,r,hkf.mono hle,?_,her,?_⟩)
    · rw [←hs,List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).1]; exact hr
    · rw [←hs]; exact hcomp.append

theorem CtaBarSources.ref_cta {c : Nat} {record : CtaBarrier.Record EvId} {e : EvId}
    (hs : CtaBarSources L X c record) (he : e ∈ record.refs) : e.1/L.block = c := by
  have localToCta {g : Nat} (hg : g < L.block) (hthread : e.1 = c*L.block+g) : e.1/L.block = c := by
    have hb : 0 < L.block := by omega
    rw [hthread,Nat.add_comm,Nat.add_mul_div_right _ _ hb,Nat.div_eq_of_lt hg,Nat.zero_add]
  cases record with
  | exit g f =>
    have heq : e = f := by simpa [CtaBarrier.Record.refs] using he
    subst f
    exact localToCta hs.1 hs.2.1
  | arrival id w count lanes =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    exact localToCta (hs p hp).1 (hs p hp).2.1

theorem CtaBarHistoryOk.ref_cta {L : Launch} {X : Execution}
    (hh : CtaBarHistoryOk L X) {c : Nat} {r : CtaBarrier.Record EvId} {e : EvId}
    (hr : r ∈ X.barriers c) (he : e ∈ r.refs) : e.1/L.block = c := by
  have hc : c < L.grid := by
    by_contra hn
    rw [hh.1 c (by omega)] at hr
    cases hr
  exact ((hh.2 c hc).2.1 r hr).ref_cta he

/-- A recorded generation already supplies its actual source arrival operands. -/
theorem CtaBarHistoryOk.generation_barrier {L : Launch} {X : Execution}
    (hh : CtaBarHistoryOk L X) {c id phase : Nat} {e : EvId}
    (hg : CtaBarrier.GenerationOf L.block (X.barriers c) e id phase) :
    ∃ count pc, X.IsBarArrival e id count pc := by
  obtain ⟨i,s,warp,count,lanes,g,hi,_,he,_⟩ := hg
  have hc : c < L.grid := by
    by_contra hn
    rw [hh.1 c (by omega)] at hi
    cases hi
  have hs := ((hh.2 c hc).2.1 _ (List.mem_of_getElem? hi)) (g,e) he
  exact ⟨count,hs.2.2⟩

/-- Pack an actual named resource ID and generation into the adapter's key. -/
theorem CtaBarArrivalK.of_generation {L : Launch} {X : Execution} {e : EvId} {id phase : Nat}
    (hh : CtaBarHistoryOk L X) (he : e.1 < L.threads) (hid : id < 16)
    (hg : CtaBarrier.GenerationOf L.block (X.barriers (e.1/L.block)) e id phase) :
    CtaBarArrivalK L X e (id+16*phase) := by
  have hmod : (id+16*phase)%16 = id := by omega
  have hdiv : (id+16*phase)/16 = phase := by omega
  refine ⟨he,?_,?_⟩
  · rw [hmod]
    exact hh.generation_barrier hg
  · rw [hmod,hdiv]
    exact hg

/-- The last event of thread `g`, if a `bar.arrive`, is recorded in its CTA's history. -/
def ArriveRecordedLast (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ pc id count, X.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id count .arrive⟩ →
    (g, (X.tr g).length - 1) ∈ (X.barriers (g / L.block)).flatMap CtaBarrier.Record.refs

/-- A last event other than a `bar.arrive` needs no record. -/
theorem ArriveRecordedLast.of_last {g : Nat} {q : Event}
    (h : X.get (g, (X.tr g).length - 1) = some q) (hq : ∀ id c, q.kind ≠ .bar id c .arrive) :
    ArriveRecordedLast L X g := by
  intro pc id count h'
  rw [h] at h'
  cases h'
  exact (hq id count rfl).elim

/-- In an execution without `bar.arrive` events every last event is recorded as needed. -/
theorem ArriveRecordedLast.of_none {g : Nat}
    (h : ∀ v pc id c, X.get v ≠ some ⟨pc, .bar id c .arrive⟩) : ArriveRecordedLast L X g :=
  fun pc id count h' => (h _ pc id count h').elim

/-- Every passed `bar.arrive` (one followed by another event of its thread) is recorded in its
CTA's history: the arrival is performed when the instruction executes. This is the record half of
the barrier needs of a returned `bar.arrive` (`KindNeeds`, `ctaBarWarpNeeds`), which
`DependencyOk.ready` demands of it. -/
def ArriveRecorded (L : Launch) (X : Execution) : Prop :=
  ∀ e id count pc, X.get e = some ⟨pc, .bar id count .arrive⟩ → e.2 + 1 < (X.tr e.1).length →
    e ∈ (X.barriers (e.1 / L.block)).flatMap CtaBarrier.Record.refs

/-- Keeping the resource histories while adding at most one event per thread, after a last
event that is no unrecorded `bar.arrive`, keeps every passed `bar.arrive` recorded. -/
theorem ArriveRecorded.preserving (hb : ArriveRecorded L X) (h : X.le Y)
    (hbar : Y.barriers = X.barriers) (hone : ∀ g, (Y.tr g).length ≤ (X.tr g).length + 1)
    (hlast : ∀ g, (X.tr g).length < (Y.tr g).length → ArriveRecordedLast L X g) :
    ArriveRecorded L Y := by
  intro e id count pc h3 h2
  rw [hbar]
  obtain ⟨s, hs⟩ := h.1 e.1
  have h1 := hone e.1
  have hlt : e.2 < (X.tr e.1).length := by omega
  have hget : Y.get e = X.get e := by
    unfold Execution.get; rw [← hs, List.getElem?_append_left hlt]
  rw [hget] at h3
  by_cases hx : e.2 + 1 < (X.tr e.1).length
  · exact hb e id count pc h3 hx
  · have he : e.2 = (X.tr e.1).length - 1 := by omega
    have hr := hlast e.1 (by omega) pc id count (by rw [← he]; exact h3)
    rwa [← he] at hr

/-- A returned `bar.arrive` is recorded, from the dependency axiom: each lane of its warp needs a
record of its CTA's history that holds it (`ctaBarWarpNeeds`). -/
theorem ArriveRecorded.of_consistent {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) : ArriveRecorded L X := by
  intro e id count pc he hl
  have hth : e.1 < L.threads := by
    by_contra hn
    rw [hX.outside e.1 (by omega)] at hl
    simp at hl
  have hb : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h | h
    · unfold Launch.threads at hth
      rw [h, Nat.mul_zero] at hth
      omega
    · exact h
  have hw : 0 < warpSize L e.1 := by
    rw [warpSize, Nat.lt_min]
    refine ⟨by omega, ?_⟩
    have h1 : e.1 % L.block / 32 * 32 ≤ e.1 % L.block := Nat.div_mul_le_self _ _
    have h2 := Nat.mod_lt e.1 hb
    omega
  have hret : Returned X e := by
    simp [Returned, he, Kind.resume, hl]
  have hEq : Needs L X e = ctaBarWarpNeeds L X e := by
    unfold Needs
    rw [he]
    simp [KindNeeds, ctaBarNeeds]
  have hmem : Need.node (fun x => ∃ i, ∃ r : CtaBarrier.Record EvId, ∃ y,
      (X.barriers (e.1 / L.block))[i]? = some r ∧ e ∈ r.refs ∧ x = .thread y ∧
        y.1 = warpLane L e.1 0 ∧
        (y ∈ r.refs ∨ ∃ (j g : Nat), j < i ∧ (X.barriers (e.1 / L.block))[j]? =
          some (CtaBarrier.Record.exit g y))) ∈ Needs L X e := by
    rw [hEq]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr hw, rfl⟩, rfl⟩
  obtain ⟨x, -, i, r, y, hi, her, -⟩ := hX.dependency.ready e hret _ hmem
  exact List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hi, her⟩

end PTX
