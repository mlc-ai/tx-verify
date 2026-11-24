-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Async.AsyncChain
public import Lemmas.Async.AsyncMBarrier
public import Lemmas.Order.CommitOperandOrder
public import Lemmas.Tensor.TensorCopySize
public import Lemmas.TensorStore.TensorStoreSize

@[expose] public section

namespace PTX
noncomputable section
open AsyncCopy

/-- The destination of a linear operation has at most one element per byte. -/
theorem Spec.elems_length_le (s : Spec) : s.elems.length ≤ s.dst.size := by
  have hlen : s.elems.length = s.elemOffsets.length := List.length_map ..
  rw [hlen]
  unfold Spec.elemOffsets
  cases hw : s.writes with
  | whole => simp
  | masked m =>
    exact (List.length_filter_le _ _).trans (by simp)
  | reduce r =>
    simp only [List.length_map, List.length_range]
    rcases Nat.eq_zero_or_pos (r.type.width / 8) with h | h
    · rw [h, Nat.div_zero]
      simp
    · exact Nat.div_le_self _ _

/-- Observing this copy's completion entails actual read and write effects, of equal bytes. -/
theorem Consistent.copy_effects {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hc : Consistent L K A mem0 X) {copy waiter : EvId}
    {acq : Bool} {ws : MbarScope} (ho : AsyncObserved X copy (.notify .copy) waiter acq ws)
    (hform : ∀ s, issuedBy X copy = some s → s.data = none ∧ s.writes = .whole ∧
      s.src.size = s.dst.size) :
    ∃ s bs, X.Copy copy s ∧
      X.MemReads (.async copy (.read .copy)) s.src (bs.map some) ∧
      X.MemWrites (.async copy (.write .copy)) s.dst bs ∧ bs.length = s.dst.size := by
  obtain ⟨s, bs, hi, hr, hw, hn⟩ := ho.completed hc.tma.1 hform
  obtain ⟨-, hws, -⟩ := hform s hi
  obtain hcop := issuedBy_some.mp hi
  exact ⟨s, bs, hcop, ⟨s, bs, hcop, rfl, hr, rfl⟩, ⟨s, hcop, hws, rfl, hw⟩, hn⟩

/-- A present copy write contains exactly its actual source-read bytes. Completion
notification is not required for this internal data-flow fact. -/
theorem Consistent.copy_write_read {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hc : Consistent L K A mem0 X)
    {i : EvId} {dst : Acc} {bs : List Byte}
    (hw : X.MemWrites (.async i (.write .copy)) dst bs)
    (hform : ∀ s, issuedBy X i = some s → s.data = none ∧ s.writes = .whole ∧
      s.src.size = s.dst.size) :
    ∃ s, X.Copy i s ∧ X.MemReads (.async i (.read .copy)) s.src (bs.map some) ∧
      bs.length = s.dst.size := by
  obtain ⟨s, hcop, hws, -, hbytes⟩ := hw
  obtain ⟨pc, hi⟩ := hcop
  have hn : nonempty (X.async.copies i) := ⟨.write .copy, by simp [present, hbytes]⟩
  obtain ⟨spec, hs, hok⟩ := hc.tma.1 i hn
  simp only [issuedBy, hi, Option.some.injEq] at hs
  subst hs
  obtain ⟨hd, -, hsz⟩ := hform s (issuedBy_some.mpr ⟨pc, hi⟩)
  have hsrc : sourceBytes s (X.async.copies i) = some bs := by
    have h := hok.2.2.1 bs hbytes
    rwa [hws] at h
  rw [sourceBytes, hd, hsz, Nat.sub_self, List.replicate_zero] at hsrc
  obtain ⟨rs, hrs, hbs⟩ := Option.map_eq_some_iff.mp hsrc
  rw [List.append_nil] at hbs
  subst hbs
  exact ⟨s, ⟨pc, hi⟩, ⟨s, rs, ⟨pc, hi⟩, rfl, hrs, rfl⟩, (hok.2.1 rs hrs).2.trans hsz⟩

/-- Object faults are inspected by safety even though their execution is admitted. -/
theorem object_fault_unsafe {L : Launch} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} {m : Loc} {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects m) (hf : r.fault.isSome) : Unsafe L K A mem0 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨m, r, hr, hf⟩))))))

/-- The completion predicate cannot silently discard an outstanding copy. -/
theorem Complete.copy_notified {L : Launch} {X : Execution}
    (h : Complete L X) {i : EvId} {s : AsyncCopy.Spec} {m : Loc} (hi : X.Copy i s)
    (hm : s.completion = .mbarrier m) : (X.async.copies i).notified = true := by
  have hd := ((asyncDrained_iff X).1 h.2.1).1 i s hi
  simpa [hm] using hd

/-- Pending effects are already checked for hazards. No actual write event is needed. -/
theorem pending_copy_read_race {L : Launch} {X : Execution}
    {copy reader : EvId} {s : AsyncCopy.Spec} {m l : Loc} {bs : List (Option Byte)}
    (hi : X.Copy copy s) (hw : s.writes = .whole) (hg : s.generic = false)
    (hs : s.scope = none) (hm : s.completion = .mbarrier m) (hr : X.Reads reader s.dst bs)
    (hl : s.dst.Covers l) (hp : (X.async.copies copy).notified = false)
    (ho : ¬ ProxyBefore L X reader copy l) : Race L X := by
  obtain ⟨pc, hget⟩ := hi
  have hcopy : X.Copy copy s := ⟨pc, hget⟩
  refine ⟨.async copy (.write .copy), .thread reader, s.dst, s.dst, l, ?_, ⟨rfl, rfl⟩, hl, ?_,
    ?_, ?_, ?_⟩
  · refine ⟨?_, true, false, ⟨rfl, s, hcopy, hw, rfl⟩, Or.inl ⟨bs, hr, rfl⟩, Or.inl rfl,
      ⟨l, hl, hl⟩⟩
    intro h
    cases h
  · rintro ⟨⟨i, j, he, -⟩ | ⟨⟨s', sc, hc', -, hsc, -⟩, -⟩, -⟩
    · cases he
    · obtain rfl := Execution.Copy.unique hcopy hc'
      rw [hs] at hsc
      cases hsc
  · have hfinished : ∀ w, ¬ AsyncFinished L X copy (.write .copy) w := by
      intro w hfin
      rw [asyncFinished_copy_of_mbarrier L hcopy hm] at hfin
      obtain ⟨ws, ⟨n', m', hn, -⟩, -⟩ := hfin
      obtain ⟨-, bytes, hy, -, hnott, -, -⟩ :=
        (notifies_copy_of_mbarrier hcopy hm (Or.inr rfl)).1 hn
      exact Bool.noConfusion (hp.symm.trans hnott)
    intro order
    obtain ⟨dst, h⟩ := order.starts
    cases dst with
    | thread j =>
      obtain ⟨-, w, hf, -⟩ := h
      exact hfinished w hf
    | async j q =>
      obtain ⟨_, -, -, edge⟩ := h.2.first
      rcases edge with ⟨w, hf, -⟩ | ⟨w, hf, -⟩
      · exact hfinished w hf
      · exact not_bulkWaitsFor_of_copy hcopy (by simp [hm]) hf.2.1
  · have hread : ∀ a, X.Intent (.thread reader) a true → ¬ a.Covers l := by
      intro a ha _
      obtain ⟨pcr, hrr⟩ := hr
      rcases ha with ⟨bs', -, hff⟩ | ⟨bs', ⟨pc', hw'⟩, -⟩ | ⟨old, new, ⟨pc', hw'⟩⟩
      · cases hff
      · rw [hrr] at hw'
        cases hw'
      · rw [hrr] at hw'
        cases hw'
    rw [ByteCausality.direct_iff_of_not_write hread]
    rintro ⟨-, h⟩
    rcases h with h | ⟨hc, -⟩
    · exact ho h
    · exact not_genericCopy_of_mbarrier hcopy hg hc
  · rintro ⟨-, hacc, -, -⟩
    obtain ⟨pcr, hrr⟩ := hr
    rcases hacc with ⟨bs', -, hff⟩ | ⟨bs', ⟨pc', hw'⟩, -⟩ | ⟨old, new, ⟨pc', hw'⟩⟩
    · cases hff
    · rw [hrr] at hw'
      cases hw'
    · rw [hrr] at hw'
      cases hw'

/-- Non-CLC instructions cannot acquire CLC effects by a fabricated record. -/
theorem Consistent.no_clc_effects {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hc : Consistent L K A mem0 X) {i : EvId}
    (hn : ∀ s targets, ¬ X.ClcIssue i s targets) :
    (X.clc i).resolved.isSome = false ∧ (X.clc i).written = ∅ ∧ (X.clc i).notified = ∅ := by
  have h : ¬ ((X.clc i).resolved.isSome ∨ (X.clc i).written.Nonempty ∨
      (X.clc i).notified.Nonempty) := by
    intro he
    obtain ⟨s, targets, hi⟩ := hc.clc.2.2.1 i he
    exact hn s targets hi
  simp only [not_or] at h
  exact ⟨Bool.eq_false_iff.mpr h.1, Finset.not_nonempty_iff_eq_empty.mp h.2.1,
    Finset.not_nonempty_iff_eq_empty.mp h.2.2⟩

/-- Only actual bulk/MMA/commit issuers can carry independent async effects. -/
theorem Consistent.nonIssuer_no_effects {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hc : Consistent L K A mem0 X) {i : EvId}
    (hbulk : issuedBy X i = none)
    (hcommit : ∀ s, ¬ X.Commit i s)
    (hclc : ∀ s targets, ¬ X.ClcIssue i s targets)
    (htensor : ∀ address s, ¬ X.TensorIssue i address s)
    (hstore : ∀ address s, ¬ X.TensorStoreIssue i address s)
    (hmma : ∀ d s accum mask, ¬ X.MmaIssue i d s accum mask)
    (hcp : ∀ c, ¬ X.CpIssue i c)
    (hshift : ∀ c, ¬ X.ShiftIssue i c)
    (harrive : ∀ m noinc, ¬ X.AsyncArrive i m noinc) : X.asyncSize i = 0 := by
  have hn : ¬ nonempty (X.async.copies i) := by
    intro h
    obtain ⟨s, hs, _⟩ := hc.tma.1 i h
    rw [hbulk] at hs
    cases hs
  have hr : (X.async.copies i).readBytes.isSome = false :=
    Bool.eq_false_iff.mpr (fun h => hn ⟨.read .copy, h⟩)
  have hw : (X.async.copies i).writeBytes.isSome = false :=
    Bool.eq_false_iff.mpr (fun h => hn ⟨.write .copy, h⟩)
  have hf : (X.async.copies i).notified = false :=
    Bool.eq_false_iff.mpr (fun h => hn ⟨.notify .copy, h⟩)
  have hew : ∀ j, (X.async.copies i).elemWrites j = none ∧
      (X.async.copies i).elemOld j = none := by
    intro j
    constructor
    · cases hh : (X.async.copies i).elemWrites j with
      | none => rfl
      | some bs => exact absurd ⟨.write (.elem j), by simp [present, hh]⟩ hn
    · cases hh : (X.async.copies i).elemOld j with
      | none => rfl
      | some bs => exact absurd ⟨.old (.elem j), by simp [present, hh]⟩ hn
  have hs : X.async.mmaStarted i = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    rcases hc.tma.2.1.1 i h with ⟨d, s, accum, mask, operands, hi, -⟩ |
      ⟨c, operands, hi, -⟩ | ⟨s, operands, hi, -⟩
    · exact hmma d s accum mask hi
    · exact hcp c hi
    · exact hshift s hi
  have hd : X.async.mmaDone i = false :=
    Bool.eq_false_iff.mpr (fun h => by have hh := hc.tma.2.1.2 i h; rw [hs] at hh; cases hh)
  have ha : X.async.arrived i = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨⟨m, noinc, hi⟩, -⟩ := hc.tma.2.2.2 i h
    exact harrive m noinc hi
  obtain ⟨cr, cw, cn⟩ := hc.no_clc_effects hclc
  have hz : X.tensor i = none := by
    cases he : X.tensor i with
    | none => rfl
    | some observation =>
      obtain ⟨address, hi⟩ := (hc.tensor i observation he).1
      exact False.elim (htensor address observation.spec hi)
  have hout : X.tensorStores i = none := by
    cases he : X.tensorStores i with
    | none => rfl
    | some observation =>
      obtain ⟨address, hi⟩ := (hc.store i observation he).1
      exact False.elim (hstore address observation.spec hi)
  have hm : X.tcNotified i = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro rank hmem
    obtain ⟨⟨s, m, hi, _⟩, _⟩ := hc.tcCommit i rank hmem
    exact hcommit s hi
  have hes : X.elemSize i = 0 := Execution.elemSize_eq_zero hew
  simp [Execution.asyncSize, hr, hw, hf, hs, hd, ha, hes, cr, cw, cn, hz, hout, hm]

theorem Consistent.failed_poll_no_effects {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hc : Consistent L K A mem0 X)
    {i : EvId} {pc parity : Nat} {m : Loc} {acquire : Bool} {scope : MbarScope}
    (hi : X.get i = some ⟨pc, .wait m parity false acquire scope⟩) : X.asyncSize i = 0 := by
  apply hc.nonIssuer_no_effects
  · simp [issuedBy, hi]
  · intro m
    simp [Execution.Commit, hi]
  · intro s targets
    simp [Execution.ClcIssue, hi]
  · intros; simp [Execution.TensorIssue, hi]
  · intros; simp [Execution.TensorStoreIssue, hi]
  · intros; simp [Execution.MmaIssue, hi]
  · intros; simp [Execution.CpIssue, hi]
  · intros; simp [Execution.ShiftIssue, hi]
  · intros; simp [Execution.AsyncArrive, hi]

/-- No asynchronous effect can precede the existence of its issuing instruction. -/
theorem Consistent.absent_no_effects {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hc : Consistent L K A mem0 X)
    {i : EvId} (hi : X.get i = none) : X.asyncSize i = 0 := by
  apply hc.nonIssuer_no_effects
  · simp [issuedBy, hi]
  · intros; simp [Execution.Commit, hi]
  · intros; simp [Execution.ClcIssue, hi]
  · intros; simp [Execution.TensorIssue, hi]
  · intros; simp [Execution.TensorStoreIssue, hi]
  · intros; simp [Execution.MmaIssue, hi]
  · intros; simp [Execution.CpIssue, hi]
  · intros; simp [Execution.ShiftIssue, hi]
  · intros; simp [Execution.AsyncArrive, hi]

/-- The constant part of `Execution.asyncSize_le`: a tensor load and a tensor store of at
most `256 ^ 5 * 8` bytes each, the element stages of a linear operation whose destination is
bounded by its 32-bit size operand, a commit's 16 deliveries and fixed stages. -/
def asyncStageBound : Nat := 4 * (256 ^ 5 * 8) + 2 * 2 ^ 32 + 26

/-- CLC contributes at most two stages per grid CTA plus resolution. A tensor
copy contributes at most 2 * (256 ^ 5 * 8) + 1 stages, from descriptor box limits (rank at
most 5) and the represented format widths. Output copies add at most the same byte count
plus two completion stages. A linear operation adds at most two element stages per destination
byte. A commit adds at most 16 target deliveries. This deliberately loose
sum is a bound, not an execution restriction. -/
theorem Execution.asyncSize_le (X : Execution) (i : EvId)
    {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hc : Consistent L K A mem0 X) (hcopy : ∀ s, X.Copy i s → s.dst.size ≤ 2 ^ 32) :
    X.asyncSize i ≤ asyncStageBound + 2 * L.grid := by
  have hw : (X.clc i).written ⊆ Finset.range L.grid := by
    intro c hm
    obtain ⟨s, ts, hi⟩ := hc.clc.2.2.1 i (.inr (.inl ⟨c, hm⟩))
    have he := (hc.clc.2.2.2.1 i s ts hi).1
    obtain ⟨⟨_, _, _, _, _, _, hlt, _⟩, _⟩ := he.writes c hm
    exact Finset.mem_range.mpr hlt
  have hn : (X.clc i).notified ⊆ (X.clc i).written := by
    intro c hm
    obtain ⟨s, ts, hi⟩ := hc.clc.2.2.1 i (.inr (.inr ⟨c, hm⟩))
    exact (hc.clc.2.2.2.1 i s ts hi).1.notified c hm
  have hcw : (X.clc i).written.card ≤ L.grid := by simpa using Finset.card_le_card hw
  have hcn := (Finset.card_le_card hn).trans hcw
  have helem : X.elemSize i ≤ 2 * 2 ^ 32 := by
    unfold Execution.elemSize
    split
    · rename_i pc s hget
      have h1 : (List.range s.elems.length).countP
          (fun j => ((X.async.copies i).elemWrites j).isSome) ≤ s.elems.length :=
        (List.countP_le_length (l := List.range s.elems.length)).trans (by simp)
      have h2 : (List.range s.elems.length).countP
          (fun j => ((X.async.copies i).elemOld j).isSome) ≤ s.elems.length :=
        (List.countP_le_length (l := List.range s.elems.length)).trans (by simp)
      have h3 : s.elems.length ≤ s.dst.size := Spec.elems_length_le s
      have h4 : s.dst.size ≤ 2 ^ 32 := hcopy s ⟨pc, hget⟩
      omega
    · omega
  have hts : ((X.tensor i).map fun observation => observation.effects.size).getD 0 ≤
      (2 * (256 ^ 5 * 8) + 1) := by
    cases he : X.tensor i with
    | none => simp
    | some observation =>
      have hv := (hc.tensor i observation he).2.2.2
      have hb := TensorTransfer.bytes_le_of_valid hv
      have hs := observation.effects.size_le
      change observation.effects.size ≤ (2 * (256 ^ 5 * 8) + 1)
      omega
  have hstore : ((X.tensorStores i).map fun observation => observation.effects.size).getD 0 ≤
      (2 * (256 ^ 5 * 8) + 2) := by
    cases he : X.tensorStores i with
    | none => simp
    | some observation =>
      have hv := (hc.store i observation he).2.1.1
      have hb := TensorTransfer.bytes_le_of_valid hv
      have hs := observation.effects.size_le
      change observation.effects.size ≤ (2 * (256 ^ 5 * 8) + 2)
      omega
  have hmulti : (X.tcNotified i).card ≤ 16 :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin 16)
  unfold Execution.asyncSize asyncStageBound
  split_ifs <;> omega

end
end PTX
