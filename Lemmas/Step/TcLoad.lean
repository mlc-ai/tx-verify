-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Issue
public import Lemmas.Tcgen05.TcMmaSource
public import Lemmas.Tcgen05.TcIssueExtend
public import Lemmas.Tcgen05.TcCollExtend
public import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting

@[expose] public section

/-! # Issuing a Tensor Core instruction as a progress step

A proof tool. A Tensor Core instruction one lane issues alone (an MMA, a commit, a copy, a shift)
is appended in a safe prefix (`tc_counted_extension`); its completion is a separate step. A
warp-collective `tcgen05` instruction is appended given the Tensor Memory allocator result and read
obligation of the extended execution (`tccoll_counted_extension`).

A thread whose last event is released can issue `tcgen05.ld` of any shape
(`tc_load_counted_extension`): the execution with the load appended is consistent and strictly
larger, when each register slot returns the value the last write of its cell (`tcDataCell` of the
load's shape) left (`TcMma.LastWrote`) and that value is a whole word. The value a read source of
the new load wrote is the value the last write of the cell left (`readSource_snoc_ld`): the source
is old, its write order and its stability restrict to the original execution, and no write can
follow the load, which has no later wait and no successor. The words `loadVals` take, for each
slot, that value when there is one; it is unique (`lastWrote_unique`). -/

namespace PTX.Step
open PTX AsyncCopy TcMma
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution} {mem0 : Mem0} {g : Nat}

open Classical in
/-- The words of a load of shape `sh` of thread `g` at `address`: in slot `j`, the value the last
write of its cell left, when there is one. -/
def loadVals (L : Launch) (A : List Assumption) (X : Execution) (g : Nat) (sh : TcShape)
    (address n : Nat) : List Value :=
  (List.range n).map fun j =>
    if h : ∃ v, LastWrote L A X (tcDataCell L g sh address j) v then Classical.choose h
    else .bits 32 0

theorem loadVals_length {sh : TcShape} {address n : Nat} :
    (loadVals L A X g sh address n).length = n := by
  simp [loadVals]

/-- **The words of a load are the last writes' values.** -/
theorem loadVals_spec (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (hinj : LayoutInjective X)
    {sh : TcShape} {address n j : Nat} {v : Value} (hj : j < n)
    (hv : LastWrote L A X (tcDataCell L g sh address j) v) :
    (loadVals L A X g sh address n)[j]? = some v := by
  have hex : ∃ v, LastWrote L A X (tcDataCell L g sh address j) v := ⟨v, hv⟩
  simp only [loadVals, List.getElem?_map, List.getElem?_range hj, Option.map_some, hex,
    ↓reduceDIte, Option.some.injEq]
  exact lastWrote_unique hX hg hinj (Classical.choose_spec hex) hv

/-- An event of an extension that is not the new one is an old event. -/
private theorem get_old {r : Nat → Option Ref} {e : Event} {v : EvId} {ev : Event}
    (h : (X.snoc g e r).get v = some ev) (hne : ev ≠ e) :
    v.2 < (X.tr v.1).length ∧ X.get v = some ev := by
  rcases snoc_get_cases h with ⟨-, rfl⟩ | h'
  · exact absurd rfl hne
  · exact h'

/-- **A read source of an appended load is a last write of the original execution**: the value it
wrote is the value the last write of the cell left. -/
theorem readSource_snoc_ld (ht : CommitOk X) (ho : ObjectsOk X) {pc address : Nat}
    {vals : List Value} {sh : TcShape}
    {r : Nat → Option Ref}
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g ⟨pc, .tc (.ld address vals sh)⟩ r) x f ↔ baseCausality L X x f))
    {source : EvId} {cell : Cell} {v : Value}
    (hs : ReadSource L (X.snoc g ⟨pc, .tc (.ld address vals sh)⟩ r) .ld source
      (g, (X.tr g).length) cell)
    (hw : Wrote L A (X.snoc g ⟨pc, .tc (.ld address vals sh)⟩ r) source cell v) :
    LastWrote L A X cell v := by
  have hp := readPreserved_snoc (e := ⟨pc, .tc (.ld address vals sh)⟩) (r := r) ht ho hbo
  obtain ⟨-, hwr, -, hstable, -⟩ := readSource_ld.mp hs
  have hso : source.2 < (X.tr source.1).length := by
    rcases hwr with ⟨_, _, _, _, _, _, ⟨_, hm⟩, _⟩ | ⟨_, _, _, _, ⟨_, hm⟩, _⟩ |
        ⟨_, _, _, _, ⟨_, hm⟩, _⟩ | ⟨_, ⟨_, hm⟩, _⟩ <;>
      exact (get_old hm (by simp)).1
  refine ⟨source, hp.wrote hso hw, fun o hox => ?_⟩
  have hoo := tmemWrite_lt hox
  rcases hstable o (hp.tmemWrite hox) with h1 | h1 | h1 | ⟨-, h1, -⟩
  · exact .inl h1
  · exact .inr (hp.writeBefore hso h1).1
  · obtain ⟨w, ⟨pcw, hwg⟩, hw1, hw2, -⟩ := h1
    have hl := len_of_get hwg
    obtain ⟨gw, iw⟩ := w
    simp only at hw1 hw2 hl
    subst hw1
    simp [snoc_len] at hl
    omega
  · have := (tcStep_path_events ((hp.tcFrame.tcBefore hoo).mp h1).tcStep).1
    simp at this

/-- **A released thread issues a Tensor Core instruction of its own lane** (no warp-collective
`tcgen05` event): a counted extension of a prefix whose conflicts at read bytes are ordered. -/
theorem tc_counted_extension_reads (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X)
    (hg : g < L.threads) (hne : X.tr g ≠ []) (hrel : Released L X g)
    {t t1 : TState} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {pc : Nat} {k : TcKind}
    (he : EStep K A L g t1 ⟨pc, .tc k⟩ o) (hcoll : isTcColl ⟨pc, .tc k⟩ = false)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .tc k⟩ (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g ⟨pc, .tc k⟩ (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hld : ∀ pc' ta vals sh, (⟨pc, .tc k⟩ : Event) ≠ ⟨pc', .tc (.ld ta vals sh)⟩ := by
    intro pc' ta vals sh h
    cases h
    simp [isTcColl] at hcoll
  have hextra : ExtensionObligations L A (X.snoc g ⟨pc, .tc k⟩ (fun _ => none)) :=
    ExtensionObligations.snoc_frame hX nofun nofun nofun (ClcOk.snoc hX.clc (.inl hne) nofun)
      (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc nofun nofun nofun nofun hld)
      (hX.atomic.snoc hX.store hX.tma.1 nofun) (hX.fenceSc_snoc nofun nofun nofun nofun)
      (hX.matrix.snoc rfl) (fun _ h => Kind.noConfusion h)
  refine ⟨_, consistent_tcissue_snoc_reads hX hg hrun hl he rfl hcoll hord hrel.ready
    hextra hasm (tmaOk_snoc_tc hX.tma hX.tcCommit rfl) hsg, le_snoc, ?_⟩
  rw [size_snoc hX hg rfl]
  omega

/-- `tc_counted_extension_reads` for a safe prefix. -/
theorem tc_counted_extension (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X)
    (hr : ¬ Race L X) (hst : StrongOrdered L X) (hg : g < L.threads) (hne : X.tr g ≠
      []) (hrel : Released L X g)
    {t t1 : TState} {o : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {pc : Nat} {k : TcKind}
    (he : EStep K A L g t1 ⟨pc, .tc k⟩ o) (hcoll : isTcColl ⟨pc, .tc k⟩ = false)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .tc k⟩ (fun _ => none)))
    (hsg : SyncGuarded L K (X.snoc g ⟨pc, .tc k⟩ (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  tc_counted_extension_reads hX (.of_safe hm hr hst) hg hne hrel hrun hl he hcoll hasm hsg

/-- An appended `tcgen05` event other than a load keeps the Tensor Core read obligation. -/
theorem _root_.PTX.Consistent.tcRead_snoc_tc (hX : Consistent L K A mem0 X) {pc : Nat}
    {k : TcKind} {r : Nat → Option Ref} (hk : ∀ ta vals sh, k ≠ .ld ta vals sh) :
    TcMma.ReadOk L A (X.snoc g ⟨pc, .tc k⟩ r) :=
  hX.tcRead_snoc nofun nofun nofun nofun fun _ ta vals sh h => hk ta vals sh (by cases h; rfl)

/-- **A released thread performs a warp-collective `tcgen05` instruction**, given the Tensor
Memory allocator result and read obligation of the extended execution: a counted extension. -/
theorem tccoll_counted_extension (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g)
    {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    {pc : Nat} {k : TcKind} (he : EStep K A L g t1 ⟨pc, .tc k⟩ o)
    (hcoll : isTcColl ⟨pc, .tc k⟩ = true)
    (hres : Tmem.Pair.ResultOk L (X.snoc g ⟨pc, .tc k⟩ (fun _ => none)))
    (hread : TcMma.ReadOk L A (X.snoc g ⟨pc, .tc k⟩ (fun _ => none)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .tc k⟩ (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have htma : TmaOk (X.snoc g ⟨pc, .tc k⟩ (fun _ => none)) := tmaOk_snoc_tc hX.tma hX.tcCommit rfl
  have hextra : ExtensionObligations L A (X.snoc g ⟨pc, .tc k⟩ (fun _ => none)) :=
    ExtensionObligations.snoc_frame hX nofun nofun nofun (ClcOk.snoc hX.clc hne nofun) hres hread
      (hX.atomic.snoc hX.store hX.tma.1 nofun) (hX.fenceSc_snoc nofun nofun nofun nofun)
      (hX.matrix.snoc rfl) (fun _ h => Kind.noConfusion h)
  refine ⟨_, consistent_tccoll_snoc_of_orderOk hX hg hrun hl he hcoll hrel.ready
    ((snoc_tccoll_sinkFrame hX hg hcoll).orderOk hX.orderOk)
    hextra hasm htma, le_snoc, ?_⟩
  rw [size_snoc hX hg rfl]
  omega

/-- **A released thread issues a Tensor Memory load**: a counted extension, when each slot returns
the whole word the last write of its cell left. -/
theorem tc_load_counted_extension (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ []) (hrel : Released L X g) {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    {pc address : Nat} {vals : List Value} {sh : TcShape}
    (he : EStep K A L g t1 ⟨pc, .tc (.ld address vals sh)⟩ o)
    (hvals : ∀ j v, j < vals.length → LastWrote L A X (tcDataCell L g sh address j) v →
      vals[j]? = some v ∧ v.bytes = 4)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .tc (.ld address vals sh)⟩ (fun _ => none))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let ev : Event := ⟨pc, .tc (.ld address vals sh)⟩
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g ev (fun _ => none)) x f ↔ baseCausality L X x f) :=
    fun hb => baseCausality_snoc_old_of_not_arrive (e := ev) hX.cluster (.of_rfWf hX.rf)
      (fun _ _ h => Kind.noConfusion h) (fun _ _ _ h => Kind.noConfusion h)
      (fun _ _ _ _ h => Kind.noConfusion h) (fun _ h => Kind.noConfusion h) hb
  have hread : TcMma.ReadOk L A (X.snoc g ev (fun _ => none)) := by
    refine readOk_snoc hX.tcRead hX.tcCommit hX.tma.2.2.1 hX.tma.2.1 hbo ?_
    intro pc' a vs sh' hev j source cell value hc hs hw
    simp only [ev, Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at hev
    obtain ⟨-, rfl, rfl, rfl⟩ := hev
    obtain ⟨a', vs', sh'', ⟨pc'', hl'⟩, hj, rfl⟩ := hc
    rcases snoc_get_cases hl' with ⟨-, hev'⟩ | ⟨hold, -⟩
    · simp only [ev, Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at hev'
      obtain ⟨-, rfl, rfl, rfl⟩ := hev'
      obtain ⟨hget, hbytes⟩ := hvals j value hj (readSource_snoc_ld hX.tcCommit
        hX.tma.2.2.1 hbo hs hw)
      exact ⟨value, hget, .inl ⟨hbytes, rfl⟩⟩
    · simp at hold
  exact tccoll_counted_extension hX hg (.inl hne) hrel hrun hl he rfl
    (hX.tmemPairResult.snoc_not_wr nofun) hread hasm

end
end PTX.Step
