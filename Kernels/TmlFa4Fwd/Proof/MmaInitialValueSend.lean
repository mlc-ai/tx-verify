-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaInitialValueCursor
public import Kernels.TmlFa4Fwd.Proof.MmaValueDescriptorWord
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

def valueDescriptorEvent (l : Launch) (steady : Bool) (recv : Value) (ok : Bool) : Event :=
  ⟨(valueDescriptorSite steady).prepare + 8,
    .shfl .idx (b32 (valueDescriptorLow l 1)) 0 31 recv ok⟩

/-- A lane which proceeds from its initial slot-one acquire to a PV operation
sends the physical slot-one descriptor through the actual lane-zero broadcast. -/
theorem initialValueSendAfterReady {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (steady : Bool) {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s ((waitSite (initialValueWaitSite steady)).pc + 3)
      (initialValueWaitFacts l steady)) (hw : Walk kernel Assumptions.all l g s es vs)
    {later : Event} (hLater : later ∈ es)
    (hAbove : (valueDescriptorSite steady).prepare + 8 < later.pc) :
    ∃ u pre tail post recv ok, es = pre ++ valueDescriptorEvent l steady recv ok :: tail ∧
      At u ((valueDescriptorSite steady).prepare + 9)
        [((valueDescriptorSite steady).output, recv), (1062, b32 12)] ∧
      Walk kernel Assumptions.all l g u tail post ∧ later ∈ tail ∧
      ∀ v ∈ pre, v.pc < (valueDescriptorSite steady).prepare+8 := by
  let site := valueDescriptorSite steady
  let start := (waitSite (initialValueWaitSite steady)).pc + 3
  change site.prepare + 8 < later.pc at hAbove
  let F := [(7207, b32 (kvSlot 1)), (2535, b32 l.sharedBase), (1062, b32 12)]
  have hBounds : 1907 ≤ start ∧ start ≤ site.prepare ∧ site.prepare + 9 < 2768 := by
    cases steady <;> decide
  have hPrepare : 1907 ≤ site.prepare := hBounds.1.trans hBounds.2.1
  have hF : Holds s.regs F := by
    have hRegs := hs.2.2.2.2
    exact ⟨hRegs.2.1, hRegs.2.2.2.1, hRegs.2.2.2.2.1, trivial⟩
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩, hF.2.2.1⟩
  have hAudit : ((kernel.code.drop start).take (site.prepare - start)).all
      (pvCutCode start site.prepare (F.map Prod.fst)) = true := by
    cases steady <;> set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t, pre, rest, visits, hSplit, htPc, htShape, htF, htWalk, htLater, hBefore⟩ :=
    pvWalkCut hBounds.1 (by omega) hAudit hw (show start ≤ s.pc ∧ s.pc ≤ site.prepare by
      rw [hs.1]; exact ⟨le_rfl, hBounds.2.1⟩) hShape hF hLater (by omega)
  have ht : At t site.prepare F :=
    ⟨htPc, htShape.1.2.2 (by rw [htPc]; cases steady <;> decide), htShape.1.2.1,
      normalBeforeLaterEvent htWalk htLater (by rw [htPc]; omega), htF⟩
  obtain ⟨v, hLocal, hv⟩ := valueDescriptorLocal hp g steady 1 t ht
  have hStraight : ((kernel.code.drop site.prepare).take (7-1)).all
      (fun i => schedulerFallsThrough i.op) = true := by
    cases steady <;> set_option maxRecDepth 100000 in kernel_rfl
  have hLocal' := localRun (show 1904 ≤ site.prepare by omega) (by omega) htPc hStraight hLocal
  rcases advanceWalkLocals hLocal' htWalk with hEmpty | ⟨post, _, _, hvWalk⟩
  · rw [hEmpty] at htLater
    cases htLater
  let G := [(site.input, b32 (valueDescriptorLow l 1)), (1062, b32 12)]
  have hAudit' : ((kernel.code.drop (site.prepare+7)).take ((site.prepare+8)-(site.prepare+7))).all
      (pvCutCode (site.prepare+7) (site.prepare+8) (G.map Prod.fst)) = true := by
    cases steady <;> set_option maxRecDepth 100000 in kernel_rfl
  have hvShape : RoleShape v ∧ v.regs 1062 = some (b32 12) :=
    ⟨⟨hv.2.1.symm ▸ Nat.zero_le _, hv.2.2.1, fun _ => hv.2.1⟩, hv.2.2.2.2.2.1⟩
  have hvPc : v.pc = site.prepare+7 := hv.1
  have hvBounds : site.prepare+7 ≤ v.pc ∧ v.pc ≤ site.prepare+8 := by
    rw [hvPc]
    exact ⟨le_rfl, Nat.le_succ _⟩
  obtain ⟨b, pre', tail, bVisits, hTail, hbPc, hbShape, hbF, hbWalk, hbLater, hbBefore⟩ :=
    pvWalkCut (show 1907 ≤ site.prepare+7 by omega) (show site.prepare+8 < 2768 by omega)
      hAudit' hvWalk hvBounds hvShape hv.2.2.2.2 htLater (by omega)
  have hBeyond : b.pc < later.pc := by rw [hbPc]; exact hAbove
  have hb : At b (site.prepare+8) G :=
    ⟨hbPc, hbShape.1.2.2 (by omega), hbShape.1.2.1,
      normalBeforeLaterEvent hbWalk hbLater hBeyond, hbF⟩
  have hb' : At b (site.prepare+8) [(site.input, b32 (valueDescriptorLow l 1))] :=
    hb.mono ⟨hbF.1,trivial⟩
  obtain ⟨u, ev, final, uVisits, hE, hf, _, hUWalk, hULater⟩ :=
    pvWalkEvent hbWalk (valueDescriptorShuffle hp steady 1 hb') hbLater hBeyond
  obtain ⟨recv, ok, rfl, hNew⟩ := hf
  obtain rfl := Option.some.inj hNew
  have hR : At b (site.prepare+8) [(1062, b32 12)] := hb.mono ⟨hbF.2.1,trivial⟩
  have hDistinct : ∀ pair ∈ [(1062, b32 12)], pair.1 ≠ site.output := by
    cases steady <;> simp [site, valueDescriptorSite]
  refine ⟨_, pre++pre', final, uVisits, recv, ok, by
    simp [hSplit, hTail, hE, hbPc, valueDescriptorEvent, site, List.append_assoc],
    hR.set hDistinct, hUWalk, hULater, ?_⟩
  intro v hm
  rcases List.mem_append.mp hm with h | h
  · exact (hBefore v h).trans (Nat.lt_add_of_pos_right (by decide))
  · exact hbBefore v h

/-- A later recorded event that has completed both initial ready acquisitions
carries the actual first value descriptor send in its prefix. -/
theorem initialValueSendBeforeEventInWalk {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g index : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 1908 (readyFrame l)) (hw : Walk kernel Assumptions.all l g s es vs)
    {later : Event} (he : es[index]? = some later) (hAbove : 2559 < later.pc)
    (hTwo : 1 < ((es.take index).filterMap readyEvent).length) :
    ∃ steady u recv ok pre tail post, es = pre ++ valueDescriptorEvent l steady recv ok :: tail ∧
      pre.length < index ∧
      At u ((valueDescriptorSite steady).prepare + 9)
        [((valueDescriptorSite steady).output, recv), (1062, b32 12)] ∧
      Walk kernel Assumptions.all l g u tail post := by
  obtain ⟨suffix, hPrefix⟩ := List.take_prefix index es
  have hCount : 1 < (es.filterMap readyEvent).length := by
    have h := congrArg (fun l => (l.filterMap readyEvent).length) hPrefix
    simp only [List.filterMap_append, List.length_append] at h
    omega
  obtain ⟨steady, before, rest, hEvent, hKey, hAfter⟩ :=
    initialValueSuccessFromEntry hp hs hw hCount
  have hEnd : before.length < index := by
    by_contra! h
    have hTake : es.take index = before.take index := by
      rw [hEvent, List.take_append_of_le_length h]
    obtain ⟨remaining, hRemain⟩ := List.take_prefix index before
    have hb := congrArg (fun es => (es.filterMap readyEvent).length) hRemain
    simp only [List.filterMap_append, List.length_append, hKey, List.length_singleton] at hb
    rw [hTake] at hTwo
    omega
  have hLookup : rest[index-(before.length+1)]? = some later := by
    have h : (es.drop (before.length+1))[index-(before.length+1)]? = some later := by
      rwa [List.getElem?_drop, Nat.add_sub_of_le (show before.length+1 ≤ index by omega)]
    rw [hEvent, ← List.drop_drop, List.drop_append_length] at h
    exact h
  have hLaterIn := List.mem_of_getElem? hLookup
  rcases hAfter with rfl | ⟨v, vVisits, hv, hvWalk⟩
  · cases hLaterIn
  have hCap : (valueDescriptorSite steady).prepare + 8 ≤ 2559 := by cases steady <;> decide
  have hLaterAbove := hCap.trans_lt hAbove
  obtain ⟨u, pre, tail, post, recv, ok, hSplit, hu, huWalk, _, hEarly⟩ :=
    initialValueSendAfterReady hp steady hv hvWalk hLaterIn hLaterAbove
  let seen := before ++ initialValueWaitEvent l g steady true :: pre
  have hAt : es = seen ++ valueDescriptorEvent l steady recv ok :: tail := by
    simp [seen, hEvent, hSplit, List.append_assoc]
  refine ⟨steady,u,recv,ok,seen,tail,post,hAt,?_,hu,huWalk⟩
  have hBefore : pre.length < index-(before.length+1) := by
    by_contra! h
    rcases Nat.lt_or_eq_of_le h with hLt | hEq
    · rw [hSplit, List.getElem?_append_left hLt] at hLookup
      exact (Nat.not_lt_of_ge hLaterAbove.le (hEarly later (List.mem_of_getElem? hLookup)))
    · rw [hEq, hSplit, List.getElem?_append_right le_rfl, Nat.sub_self,
        List.getElem?_cons_zero] at hLookup
      have hPc := congrArg Event.pc (Option.some.inj hLookup)
      exact (Nat.ne_of_lt hLaterAbove) hPc
  simp [seen]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Mma
