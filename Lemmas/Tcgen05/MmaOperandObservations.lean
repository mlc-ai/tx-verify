-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Tmem.TmemStore
public import Core.Tc.TcMmaDescriptor
public import Lemmas.Tcgen05.MmaCompletionFrame

@[expose] public section

section
namespace PTX.TcMma

theorem readOk_of_no_issue {L : Launch} {A : List Assumption} {X : Execution}
    (h : ∀ i d s accum mask, ¬ X.MmaIssue i d s accum mask)
    (hst : ∀ e a vals sh, ¬ X.TSt e a vals sh)
    (hcp : ∀ e c, ¬ X.CpIssue e c) (hsh : ∀ e s, ¬ X.ShiftIssue e s) : ReadOk L A X := by
  have hwrite : ∀ (w : EvId) (cell : Cell), ¬ TmemWrite L X w cell := by
    intro w cell hw
    rcases hw with ⟨d, s, accum, mask, row, col, hi, -⟩ | ⟨a, vals, sh, j, ht, -⟩ |
      ⟨c, cta, index, lane, hc, -⟩ | ⟨s, hs, -⟩
    · exact h _ _ _ _ _ hi
    · exact hst _ _ _ _ ht
    · exact hcp _ c hc
    · exact hsh _ s hs
  constructor
  · intro load address vals shape j source cell value _ _ hsrc _
    exact absurd hsrc.2.1 (hwrite source cell)
  · intro mma index cell pos source value operands _ hsrc _
    exact absurd hsrc.2.1 (hwrite source cell)

end PTX.TcMma
end

section
namespace PTX.TcMma

theorem decode_valid {group : CtaGroup} {ws : Bool} {q : MmaKind} {x : Nat} {d : Descriptor}
    (h : decode group ws q x = some d) : Valid d := by
  unfold decode at h
  split at h
  · simp at h
  · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨hg, he⟩ := h
    subst d
    exact hg.2.2.2.2

theorem decode_group {group : CtaGroup} {ws : Bool} {q : MmaKind} {x : Nat} {d : Descriptor}
    (h : decode group ws q x = some d) : d.group = group := by
  unfold decode at h
  split at h
  · simp at h
  · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨-, he⟩ := h
    subst d
    rfl

end PTX.TcMma
end

section
/-! Shape and actual byte observations follow from an actual MMA issue and its
recorded operands. These facts require consistency, not safety or completion. -/
namespace PTX
noncomputable section

/-- Operand observations of an actual MMA cannot be justified by a same-event
`tcgen05.cp`; the instruction identity also fixes their exact byte lengths. -/
theorem AsyncCopy.TcEffectsOk.mma_observation_shape {X : Execution}
    (ht : AsyncCopy.TcEffectsOk X) {i : EvId} {d : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {operands : AsyncCopy.MmaOperands}
    (hi : X.MmaIssue i d s acc mask)
    (ho : X.async.mmaOperands i = some operands) :
    TcMma.Valid s.descriptor ∧
      operands.a.length =
        (if s.descriptor.ws ∧ s.descriptor.m < 128 then 128 else s.descriptor.m)*
          s.descriptor.kind.k*s.descriptor.kind.width ∧
      operands.b.length = s.descriptor.n*s.descriptor.kind.k*s.descriptor.kind.width := by
  have hstarted : X.async.mmaStarted i = true := by
    simp only [AsyncCopy.Snapshot.mmaStarted,ho,Option.isSome_some]
  obtain ⟨pc,hget⟩ := hi
  rcases ht.1 i hstarted with
    ⟨d',s',acc',mask',ops',⟨pc',hget'⟩,ho',hvalid,ha,hb⟩ |
    ⟨c,ops',hc,ho',ha,hb⟩ | ⟨sh,ops',hsh,ho',ha,hb⟩
  · have he := Option.some.inj (hget.symm.trans hget')
    cases he
    have hops := Option.some.inj (ho'.symm.trans ho)
    cases hops
    refine ⟨hvalid,ha.trans ?_,hb.trans ?_⟩ <;>
      simp only [TcMma.Operand.bytes,TcMma.Operand.rows,TcMma.Operand.extent,
        reduceCtorEq,true_and,false_and,↓reduceIte]
  · obtain ⟨pc', hget'⟩ := hc
    have he := hget.symm.trans hget'
    cases he
  · obtain ⟨pc', hget'⟩ := hsh
    have he := hget.symm.trans hget'
    cases he

/-- A shared byte location can only be returned for an in-range flat operand
coordinate. Represented MMA rows have 32 operand bytes. -/
theorem TcMma.OperandSpec.byteLoc_index_lt {s : TcMma.OperandSpec}
    {op : TcMma.Operand} {index : Nat} {l : Loc}
    (hl : s.byteLoc op index = some l) :
    index < op.rows s.descriptor*s.descriptor.kind.k*s.descriptor.kind.width := by
  have hshape : TcMma.Valid s.descriptor ∧
      index/(s.descriptor.kind.k*s.descriptor.kind.width) < op.rows s.descriptor := by
    by_contra hn
    unfold TcMma.Operand.rows at hn
    have hnone : s.byteLoc op index = none := by
      unfold TcMma.OperandSpec.byteLoc
      dsimp only
      rw [ite_eq_left hn]
    rw [hnone] at hl
    cases hl
  have hpos : 0 < s.descriptor.kind.k*s.descriptor.kind.width := by
    cases s.descriptor.kind <;> simp [TcMma.Kind.k,TcMma.Kind.width]
  rw [Nat.mul_assoc]
  exact (Nat.div_lt_iff_lt_mul hpos).mp hshape.2

/-- Every in-range shared coordinate of an observed MMA has an actual recorded
read. Its returned byte remains open until RF and visibility determine it. -/
theorem AsyncCopy.TcEffectsOk.mma_read_exists {X : Execution}
    (ht : AsyncCopy.TcEffectsOk X) {i : EvId} {d : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {operands : AsyncCopy.MmaOperands}
    (hi : X.MmaIssue i d s acc mask)
    (ho : X.async.mmaOperands i = some operands)
    {isB : Bool} {index : Nat} {l : Loc}
    (hl : s.byteLoc (if isB then .b else .a) index = some l) :
    ∃ observed, X.MmaRead i isB index l observed ∧
      (if isB then operands.b else operands.a)[index]? = some observed := by
  obtain ⟨hvalid,ha,hb⟩ := ht.mma_observation_shape hi ho
  have hindex := TcMma.OperandSpec.byteLoc_index_lt hl
  have hbound : index < (if isB then operands.b else operands.a).length := by
    cases isB
    · simpa only [Bool.false_eq_true,↓reduceIte,TcMma.Operand.rows,
        TcMma.Operand.extent,reduceCtorEq,false_and,true_and,ha] using hindex
    · simpa only [↓reduceIte,TcMma.Operand.rows,TcMma.Operand.extent,true_and,
        reduceCtorEq,false_and,hb] using hindex
  let observed := (if isB then operands.b else operands.a)[index]'hbound
  have hget : (if isB then operands.b else operands.a)[index]? = some observed :=
    List.getElem?_eq_getElem hbound
  exact ⟨observed,⟨.inl ⟨d,s,acc,mask,hi,hl⟩,operands,ho,hget⟩,hget⟩

theorem Consistent.mma_observation_shape {L : Launch} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {i : EvId} {d : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {operands : AsyncCopy.MmaOperands}
    (hi : X.MmaIssue i d s acc mask)
    (ho : X.async.mmaOperands i = some operands) :
    TcMma.Valid s.descriptor ∧
      operands.a.length =
        (if s.descriptor.ws ∧ s.descriptor.m < 128 then 128 else s.descriptor.m)*
          s.descriptor.kind.k*s.descriptor.kind.width ∧
      operands.b.length = s.descriptor.n*s.descriptor.kind.k*s.descriptor.kind.width :=
  hX.tma.2.1.mma_observation_shape hi ho

theorem Consistent.mma_read_exists {L : Launch} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {i : EvId} {d : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {operands : AsyncCopy.MmaOperands}
    (hi : X.MmaIssue i d s acc mask)
    (ho : X.async.mmaOperands i = some operands)
    {isB : Bool} {index : Nat} {l : Loc}
    (hl : s.byteLoc (if isB then .b else .a) index = some l) :
    ∃ observed, X.MmaRead i isB index l observed ∧
      (if isB then operands.b else operands.a)[index]? = some observed :=
  hX.tma.2.1.mma_read_exists hi ho hl

/-- A source index of one Tensor Memory copy denotes at most one shared location. -/
theorem Execution.CpIssue.footprint_loc_eq {X : Execution} {i : EvId} {c : TcCopy.Spec}
    (hi : X.CpIssue i c) {index : Nat} {l l' : Loc}
    (hl : X.MmaFootprint i false index l) (hl' : X.MmaFootprint i false index l') :
    l = l' := by
  obtain ⟨tag, hi⟩ := hi
  have hloc {byte : Loc} (hf : X.MmaFootprint i false index byte) :
      (c.ctas[index / c.shape.sourceBytes]?).bind
        (fun cta => TcCopy.byteLoc c.shape c.src cta (index % c.shape.sourceBytes)) =
          some byte := by
    rcases hf with ⟨_, _, _, _, ⟨tag, h⟩, _⟩ | ⟨other, k, cta, ⟨tag, h⟩, _, hk, he, hc⟩
    · rw [hi] at h
      cases h
    · rw [hi] at h
      cases h
      rw [he, hk]
      exact hc
  exact Option.some.inj ((hloc hl).symm.trans (hloc hl'))

/-- A completed Tensor Memory copy has recorded every issued shared-source byte. -/
theorem AsyncCopy.TcEffectsOk.cp_read_of_complete {X : Execution}
    (ht : AsyncCopy.TcEffectsOk X) {i : EvId} {c : TcCopy.Spec}
    (hi : X.CpIssue i c) (hd : X.AsyncPresent i .mmaDone)
    {index : Nat} {l : Loc} (hf : X.MmaFootprint i false index l) :
    ∃ observed, X.MmaRead i false index l observed := by
  obtain ⟨site, hi⟩ := hi
  have hin : index < c.ctas.length * c.shape.sourceBytes := by
    rcases hf with ⟨_, _, _, _, ⟨tag, h⟩, _⟩ | ⟨other, k, cta, ⟨tag, h⟩, _, hk, he, _⟩
    · rw [hi] at h
      cases h
    · rw [hi] at h
      cases h
      have hpos : 0 < c.shape.sourceBytes := by cases c.shape <;> decide +revert
      apply (Nat.div_lt_iff_lt_mul hpos).mp
      rw [he]
      exact (List.getElem?_eq_some_iff.mp hk).1
  rcases ht.1 i (ht.2 i hd) with
    ⟨_, _, _, _, _, ⟨tag, h⟩, _⟩ | ⟨spec, operands, ⟨tag, h⟩, hobs, hlen, _⟩ |
    ⟨_, _, ⟨tag, h⟩, _⟩
  · rw [hi] at h
    cases h
  · rw [hi] at h
    cases h
    have hk : index < operands.a.length := hlen.symm ▸ hin
    exact ⟨operands.a[index], hf, operands, hobs, List.getElem?_eq_getElem hk⟩
  · rw [hi] at h
    cases h

end
end PTX
end
