-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Async.AsyncCopy
public import Lemmas.Clc.ClcEffects
public import Lemmas.Tensor.TensorMemory
public import Lemmas.TensorStore.TensorStore
public import Lemmas.TensorStore.TensorStoreSize
public import Lemmas.TensorStore.TensorReduce

@[expose] public section

namespace PTX
noncomputable section

/-- The event kinds whose received values `Consistent.vote` and `Consistent.warpValue` constrain:
a ballot, a mode vote, a reduction, a match and `activemask`. -/
def Kind.laneValue : Kind → Bool
  | .vote .. | .voteMode .. | .redux .. | .match_ .. | .activemask _ => true
  | _ => false

theorem laneValue_of_voteClass {k : Kind} {p : WarpPart VoteMode Bool}
    (h : voteClass k = some p) : k.laneValue = true := by
  cases k <;> simp_all [voteClass, Kind.laneValue]

theorem laneValue_of_reduxClass {k : Kind} {p : WarpPart (ReduxOp × Bool) (BitVec 32)}
    (h : reduxClass k = some p) : k.laneValue = true := by
  cases k <;> simp_all [reduxClass, Kind.laneValue]

theorem laneValue_of_matchClass {k : Kind} {p : WarpPart (Bool × Bool) (BitVec 64)}
    (h : matchClass k = some p) : k.laneValue = true := by
  cases k <;> simp_all [matchClass, Kind.laneValue]

namespace Execution

/-- No issued instructions, asynchronous effects or object observations. -/
def empty : Execution where
  tr := fun _ => []
  rf := fun _ _ => none

theorem le_refl (X : Execution) : X.le X :=
  ⟨fun _ => List.prefix_refl _, fun _ _ _ => rfl, AsyncCopy.Extends.refl _,
    (fun _ => List.prefix_refl _), (fun _ => List.prefix_refl _), (fun _ => List.prefix_refl _),
    (fun _ => Clc.Extends.refl _), ⟨fun _ _ h => h, fun _ _ h => h⟩,
    TensorCopy.snapshotExtends_refl _, TensorStore.snapshotExtends_refl _,
    ⟨fun _ => List.prefix_refl _, List.prefix_refl _⟩, (fun _ _ _ _ _ _ => rfl),
    fun _ => Finset.Subset.refl _⟩

/-- Allocator histories are immutable under execution extension. -/
theorem le_tmemHistory {X Y : Execution} (h : X.le Y) (cta : Nat) :
    X.tmemHistory cta <+: Y.tmemHistory cta := h.2.2.2.2.2.2.2.2.2.2.1.1 cta

/-- Pairings are immutable under execution extension. -/
theorem le_tmemPairing {X Y : Execution} (h : X.le Y) : X.tmemPairing <+: Y.tmemPairing :=
  h.2.2.2.2.2.2.2.2.2.2.1.2

/-- Once issued, a paired instruction cannot change its peer-wait choice. -/
theorem le_tmemPairBlocks {X Y : Execution} (h : X.le Y) {i : EvId}
    {pc : Nat} {group : CtaGroup} {dst : Option Loc} {action : Tmem.Request}
    (he : X.get i = some ⟨pc, .tc (.resource group dst action)⟩) :
    Y.tmemPairBlocks i = X.tmemPairBlocks i :=
  h.2.2.2.2.2.2.2.2.2.2.2.1 i pc group dst action he

theorem le_get {X Y : Execution} (h : X.le Y) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : Y.get e = some ev := by
  obtain ⟨suffix, hs⟩ := h.1 e.1
  have hi := len_of_get he
  unfold Execution.get at he ⊢
  rw [← hs, List.getElem?_append_left hi]
  exact he

/-- A lane that exited before a shuffle instance stays so under extension. -/
theorem shflExited_mono {X Y : Execution} (h : X.le Y) {g n : Nat}
    (he : ShflExited X g n) : ShflExited Y g n := by
  obtain ⟨k, pc, hk, hc⟩ := he
  refine ⟨k, pc, le_get h hk, ?_⟩
  obtain ⟨suffix, hs⟩ := h.1 g
  have hi := len_of_get hk
  rw [← hs, List.take_append_of_le_length hi.le]
  exact hc

/-- A numbered event of a masked warp collective keeps its number under extension. -/
theorem maskK_mono {Q V : Type} {c : Kind → Option (WarpPart Q V)} {X Y : Execution}
    (h : X.le Y) {v : EvId} {m n : Nat} (hk : X.MaskK c v m n) : Y.MaskK c v m n := by
  obtain ⟨⟨ev, p, hv, hc, hm⟩, hcnt⟩ := hk
  refine ⟨⟨ev, p, le_get h hv, hc, hm⟩, ?_⟩
  obtain ⟨suffix, hs⟩ := h.1 v.1
  have hi := len_of_get hv
  rw [← hs, List.take_append_of_le_length hi.le]
  exact hcnt

/-- An event of the smaller execution has the number it has in the extension. -/
theorem maskK_of_le {Q V : Type} {c : Kind → Option (WarpPart Q V)} {X Y : Execution}
    (h : X.le Y) {v : EvId} {ev : Event} {m n : Nat} (hv : X.get v = some ev)
    (hk : Y.MaskK c v m n) : X.MaskK c v m n := by
  obtain ⟨⟨ev', p, hv', hc, hm⟩, hcnt⟩ := hk
  rw [le_get h hv] at hv'
  cases hv'
  refine ⟨⟨ev, p, hv, hc, hm⟩, ?_⟩
  obtain ⟨suffix, hs⟩ := h.1 v.1
  have hi := len_of_get hv
  rw [← hs, List.take_append_of_le_length hi.le] at hcnt
  exact hcnt

/-- A lane that exited before an instance of a masked warp collective stays so under
extension. -/
theorem maskExited_mono {Q V : Type} {c : Kind → Option (WarpPart Q V)} {X Y : Execution}
    (h : X.le Y) {g m n : Nat} (he : MaskExited c X g m n) : MaskExited c Y g m n := by
  obtain ⟨k, pc, hk, hc⟩ := he
  refine ⟨k, pc, le_get h hk, ?_⟩
  obtain ⟨suffix, hs⟩ := h.1 g
  have hi := len_of_get hk
  rw [← hs, List.take_append_of_le_length hi.le]
  exact hc

/-- An instance of a masked warp collective is kept by extension. -/
theorem maskInstance_mono {L : Launch} {Q V : Type} {c : Kind → Option (WarpPart Q V)}
    {X Y : Execution} (h : X.le Y) {g m n : Nat} {q : Q} {part : Nat → Option V}
    (hi : MaskInstance L c X g m n q part) : MaskInstance L c Y g m n q part := by
  intro lane hl
  obtain ⟨h1, h2⟩ := hi lane hl
  refine ⟨fun hb => ?_, h2⟩
  rcases h1 hb with ⟨j, pc, k, v, hj, hc, hk, hp⟩ | ⟨hx, hp⟩
  · exact .inl ⟨j, pc, k, v, le_get h hj, hc, maskK_mono h hk, hp⟩
  · exact .inr ⟨maskExited_mono h hx, hp⟩

/-- A lane that exited before an instance of a lane collective stays so in an extension that adds
no exit. -/
theorem maskExited_of_le {Q V : Type} {c : Kind → Option (WarpPart Q V)} {X Y : Execution}
    (h : X.le Y) {g m n : Nat}
    (hnew : ∀ v pc, Y.get v = some ⟨pc, .exit⟩ → X.get v = some ⟨pc, .exit⟩)
    (he : MaskExited c Y g m n) : MaskExited c X g m n := by
  obtain ⟨k, pc, hk, hc⟩ := he
  refine ⟨k, pc, hnew _ _ hk, ?_⟩
  obtain ⟨suffix, hs⟩ := h.1 g
  have hi := len_of_get (hnew _ _ hk)
  rw [← hs, List.take_append_of_le_length hi.le] at hc
  exact hc

/-- An instance of a lane collective transfers to a smaller execution when the extension adds no
event of that instance and no exit. -/
theorem maskInstance_of_le {L : Launch} {Q V : Type} {c : Kind → Option (WarpPart Q V)}
    {X Y : Execution} (h : X.le Y) {g m n : Nat} {q : Q} {part : Nat → Option V}
    (hnew : ∀ v pc k w, Y.get v = some ⟨pc, k⟩ → c k = some ⟨m, q, w⟩ →
      X.get v = some ⟨pc, k⟩)
    (hexit : ∀ v pc, Y.get v = some ⟨pc, .exit⟩ → X.get v = some ⟨pc, .exit⟩)
    (hi : MaskInstance L c Y g m n q part) : MaskInstance L c X g m n q part := by
  intro lane hl
  obtain ⟨h1, h2⟩ := hi lane hl
  refine ⟨fun hb => ?_, h2⟩
  rcases h1 hb with ⟨j, pc, k, v, hj, hc, hk, hp⟩ | ⟨hx, hp⟩
  · have hxj := hnew _ _ _ _ hj hc
    exact .inl ⟨j, pc, k, v, hxj, hc, maskK_of_le h hxj hk, hp⟩
  · exact .inr ⟨maskExited_of_le h hexit hx, hp⟩

/-- Ballot instances are kept by an extension that adds no event they name and no exit. -/
theorem voteOk_mono {L : Launch} {X Y : Execution} (hX : VoteOk L X) (h : X.le Y)
    (hnew : ∀ v pc k, Y.get v = some ⟨pc, k⟩ → k.laneValue = true → X.get v = some ⟨pc, k⟩)
    (hexit : ∀ v pc, Y.get v = some ⟨pc, .exit⟩ → X.get v = some ⟨pc, .exit⟩) :
    VoteOk L Y := by
  intro g i n pc mask a ballot hget hk part hp lane hl
  have hx := hnew _ _ _ hget rfl
  have hp' := maskInstance_of_le (c := voteClass) h ?_ hexit hp
  · exact hX g i n pc mask a ballot hx (maskK_of_le h hx hk) part hp' lane hl
  · intro v pc k w hj hc
    exact hnew v pc k hj (laneValue_of_voteClass hc)

end Execution

/-- The event kinds of `vote.sync` with a mode, `redux.sync`, `match.sync` and `activemask`. -/
def Kind.warpValue : Kind → Bool
  | .voteMode .. | .redux .. | .match_ .. | .activemask _ => true
  | _ => false

/-- The execution constraints of `vote.sync` with a mode, `redux.sync`, `match.sync` and
`activemask` (`Consistent.warpValue`). -/
abbrev WarpValueOk (L : Launch) (X : Execution) : Prop :=
  VoteModeOk L X ∧ ReduxOk L X ∧ MatchOk L X ∧ ActiveMaskOk L X

namespace Execution

/-- The constraints of `Consistent.warpValue` are kept by an extension that adds no event of
these kinds and no exit. -/
theorem warpValueOk_mono {L : Launch} {X Y : Execution} (hX : WarpValueOk L X) (h : X.le Y)
    (hnew : ∀ v pc k, Y.get v = some ⟨pc, k⟩ → k.laneValue = true → X.get v = some ⟨pc, k⟩)
    (hexit : ∀ v pc, Y.get v = some ⟨pc, .exit⟩ → X.get v = some ⟨pc, .exit⟩) :
    WarpValueOk L Y := by
  obtain ⟨hv, hr, hm, ha⟩ := hX
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g i pc mode mask a r n hget hk part hp
    have hx := hnew _ _ _ hget rfl
    have hp' := maskInstance_of_le (c := voteClass) (q := mode) h ?_ hexit hp
    · exact hv g i pc mode mask a r n hx (maskK_of_le h hx hk) part hp'
    · intro v pc' k w hj hc
      exact hnew v pc' k hj (laneValue_of_voteClass hc)
  · intro g i pc op signed mask a r n hget hk part hp
    have hx := hnew _ _ _ hget rfl
    have hp' := maskInstance_of_le (c := reduxClass) (q := (op, signed)) h ?_ hexit hp
    · exact hr g i pc op signed mask a r n hx (maskK_of_le h hx hk) part hp'
    · intro v pc' k w hj hc
      exact hnew v pc' k hj (laneValue_of_reduxClass hc)
  · intro g i pc all wide mask a r p n hget hk part hp
    have hx := hnew _ _ _ hget rfl
    have hp' := maskInstance_of_le (c := matchClass) (q := (all, wide)) h ?_ hexit hp
    · exact hm g i pc all wide mask a r p n hx (maskK_of_le h hx hk) part hp'
    · intro v pc' k w hj hc
      exact hnew v pc' k hj (laneValue_of_matchClass hc)
  · intro g i pc r hget
    exact ha g i pc r (hnew _ _ _ hget rfl)

/-- Existing reads survive extension with all bytes unchanged, including async reads. -/
theorem le_memReads {X Y : Execution} (h : X.le Y) {e : AsyncCopy.Ref} {a : Acc}
    {bs : List (Option Byte)} (he : X.MemReads e a bs) : Y.MemReads e a bs := by
  cases e with
  | thread e =>
    rcases he with ⟨pc, hp⟩ | ⟨new, hp⟩
    · exact .inl ⟨pc, le_get h hp⟩
    · obtain ⟨pc, hq⟩ := hp
      exact .inr ⟨new, pc, le_get h hq⟩
  | async i p =>
    cases p <;> simp only [Execution.MemReads] at he ⊢
    case readLoad x y k =>
      obtain ⟨o, addr, b, ho, ⟨pc, hi⟩, hl, hb, hn, hbs⟩ := he
      obtain ⟨o', ho', hg⟩ := h.2.2.2.2.2.2.2.2.1 i o ho
      exact ⟨o', addr, b, ho', ⟨pc, by rw [← Classical.choose hg]; exact le_get h hi⟩,
        by rw [← Classical.choose hg]; exact hl, TensorCopy.Observation.readByte_mono hg hb, hn,
        hbs⟩
    case readCopy =>
      obtain ⟨s, raw, ⟨pc, hb⟩, hs, hr, hbytes⟩ := he
      exact ⟨s, raw, ⟨pc, le_get h hb⟩, hs, h.2.2.1.1 i raw hr, hbytes⟩
    case oldElem j =>
      obtain ⟨s, r, raw, ⟨pc, hb⟩, hw, hj, ho, hbytes⟩ := he
      exact ⟨s, r, raw, ⟨pc, le_get h hb⟩, hw, hj, h.2.2.1.2.2.2.2.2.2.2 i j raw ho, hbytes⟩
    case mmaRead isB index =>
      obtain ⟨b, ⟨hf, operands, ho, hb⟩, hn, hbs⟩ := he
      refine ⟨b, ⟨?_, operands, h.2.2.1.2.2.2.1 i operands ho, hb⟩, hn, hbs⟩
      rcases hf with ⟨d, s, accum, mask, ⟨pc, hi⟩, hl⟩ | ⟨c, k, cta, ⟨pc, hi⟩, hb, hct, hidx, hl⟩
      · exact .inl ⟨d, s, accum, mask, ⟨pc, le_get h hi⟩, hl⟩
      · exact .inr ⟨c, k, cta, ⟨pc, le_get h hi⟩, hb, hct, hidx, hl⟩
    case readStore x y k =>
      obtain ⟨o, addr, b, ho, ⟨pc, hi⟩, hl, hb, hn, hbs⟩ := he
      obtain ⟨o', ho', hg⟩ := h.2.2.2.2.2.2.2.2.2.1 i o ho
      exact ⟨o', addr, b, ho', ⟨pc, by rw [← Classical.choose hg]; exact le_get h hi⟩,
        by rw [← Classical.choose hg]; exact hl, TensorStore.Observation.readByte_mono hg hb, hn,
        hbs⟩
    case oldStore x y k =>
      obtain ⟨o, addr, b, ho, ⟨pc, hi⟩, hred, hl, hb, hn, hbs⟩ := he
      obtain ⟨o', ho', hg⟩ := h.2.2.2.2.2.2.2.2.2.1 i o ho
      exact ⟨o', addr, b, ho', ⟨pc, by rw [← Classical.choose hg]; exact le_get h hi⟩,
        by rw [← Classical.choose hg]; exact hred, by rw [← Classical.choose hg]; exact hl,
        TensorStore.Observation.oldByte_mono hg hb, hn, hbs⟩

/-- Existing writes survive extension with their complete contents unchanged. -/
theorem le_memWrites {X Y : Execution} (h : X.le Y) {e : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte} (he : X.MemWrites e a bs) : Y.MemWrites e a bs := by
  cases e with
  | thread e =>
    rcases he with ⟨pc, hp⟩ | ⟨old, hp⟩
    · exact .inl ⟨pc, le_get h hp⟩
    · obtain ⟨pc, hq⟩ := hp
      exact .inr ⟨old, pc, le_get h hq⟩
  | async i p =>
    cases p <;> simp only [Execution.MemWrites] at he ⊢
    case writeLoad x y k =>
      obtain ⟨o, addr, b, ho, ⟨pc, hi⟩, hl, hb, hn, hbs⟩ := he
      obtain ⟨o', ho', hg⟩ := h.2.2.2.2.2.2.2.2.1 i o ho
      exact ⟨o', addr, b, ho', ⟨pc, by rw [← Classical.choose hg]; exact le_get h hi⟩,
        by rw [← Classical.choose hg]; exact hl, TensorCopy.Observation.writeByte_mono hg hb, hn,
        hbs⟩
    case writeCta c =>
      obtain ⟨s, ts, ⟨pc, hi⟩, ht, hw⟩ := he
      exact ⟨s, ts, ⟨pc, le_get h hi⟩, ht, hw.mono (h.2.2.2.2.2.2.1 i)⟩
    case writeCopy =>
      obtain ⟨s, ⟨pc, hc⟩, hw, hd, hb⟩ := he
      exact ⟨s, ⟨pc, le_get h hc⟩, hw, hd, h.2.2.1.2.1 i bs hb⟩
    case writeElem j =>
      obtain ⟨s, ⟨pc, hc⟩, hj, hw⟩ := he
      exact ⟨s, ⟨pc, le_get h hc⟩, hj, h.2.2.1.2.2.2.2.2.2.1 i j bs hw⟩
    case writeStore x y k =>
      obtain ⟨o, addr, b, ho, ⟨pc, hi⟩, hl, hb, hn, hbs⟩ := he
      obtain ⟨o', ho', hg⟩ := h.2.2.2.2.2.2.2.2.2.1 i o ho
      exact ⟨o', addr, b, ho', ⟨pc, by rw [← Classical.choose hg]; exact le_get h hi⟩,
        by rw [← Classical.choose hg]; exact hl, TensorStore.Observation.writeByte_mono hg hb, hn,
        hbs⟩

theorem le_trans {X Y Z : Execution} (hxy : X.le Y) (hyz : Y.le Z) : X.le Z := by
  refine ⟨fun g => (hxy.1 g).trans (hyz.1 g), ?_,
    hxy.2.2.1.trans hyz.2.2.1, (fun m => (hxy.2.2.2.1 m).trans (hyz.2.2.2.1 m)),
    (fun c => (hxy.2.2.2.2.1 c).trans (hyz.2.2.2.2.1 c)),
    (fun c => (hxy.2.2.2.2.2.1 c).trans (hyz.2.2.2.2.2.1 c)),
    (fun i => (hxy.2.2.2.2.2.2.1 i).trans (hyz.2.2.2.2.2.2.1 i)),
    ⟨fun task owner ho => hyz.2.2.2.2.2.2.2.1.1 task owner (hxy.2.2.2.2.2.2.2.1.1 task owner ho),
      fun request answer hr =>
        hyz.2.2.2.2.2.2.2.1.2 request answer (hxy.2.2.2.2.2.2.2.1.2 request answer hr)⟩,
    TensorCopy.snapshotExtends_trans hxy.2.2.2.2.2.2.2.2.1 hyz.2.2.2.2.2.2.2.2.1,
    TensorStore.snapshotExtends_trans hxy.2.2.2.2.2.2.2.2.2.1 hyz.2.2.2.2.2.2.2.2.2.1,
    ⟨fun cta => (le_tmemHistory hxy cta).trans (le_tmemHistory hyz cta),
      (le_tmemPairing hxy).trans (le_tmemPairing hyz)⟩,
    (fun i pc group dst action he =>
      (hyz.2.2.2.2.2.2.2.2.2.2.2.1 i pc group dst action (le_get hxy he)).trans
        (hxy.2.2.2.2.2.2.2.2.2.2.2.1 i pc group dst action he)),
    fun i => Finset.Subset.trans (hxy.2.2.2.2.2.2.2.2.2.2.2.2 i)
      (hyz.2.2.2.2.2.2.2.2.2.2.2.2 i)⟩
  rintro e k ⟨a, bs, he⟩
  exact (hyz.2.1 e k ⟨a, bs, le_memReads hxy he⟩).trans (hxy.2.1 e k ⟨a, bs, he⟩)

theorem empty_no_memReads (e : AsyncCopy.Ref) (a : Acc) (bs : List (Option Byte)) :
    ¬ empty.MemReads e a bs := by
  cases e with
  | thread e => simp [MemReads, Reads, Rmw, get, empty]
  | async i p => cases p <;> simp [MemReads, MmaRead, empty]

theorem empty_no_async (i : EvId) (p : AsyncCopy.Part) : ¬ empty.AsyncPresent i p := by
  cases p <;> simp [AsyncPresent, MmaRead, empty]

theorem empty_no_ref (e : AsyncCopy.Ref) : ¬ empty.RefPresent e := by
  cases e with
  | thread e => simp [RefPresent, get, empty]
  | async i p => exact empty_no_async i p

theorem empty_le (X : Execution) : empty.le X := by
  refine ⟨fun _ => List.nil_prefix, ?_, ?_,
    (fun _ => List.nil_prefix), (fun _ => List.nil_prefix), (fun _ => List.nil_prefix), ?_, ?_,
    ?_, ?_,
    ⟨fun _ => List.nil_prefix, List.nil_prefix⟩, ?_, ?_⟩
  · rintro e k ⟨a, bs, h⟩
    exact False.elim (empty_no_memReads e a bs h)
  · simp [AsyncCopy.Extends, empty]
  · intro i; simp [Clc.Extends, empty]
  · simp [Clc.StateExtends, empty, Clc.initial]
  · intro i old h; cases h
  · intro i old h; cases h
  · intro i pc group dst action he; cases he
  · exact fun _ => Finset.empty_subset _

end Execution
end
end PTX
