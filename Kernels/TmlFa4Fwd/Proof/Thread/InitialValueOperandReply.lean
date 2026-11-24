-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueDescriptor
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperands
public import Kernels.TmlFa4Fwd.Proof.MmaValuePackedTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma (valueDescriptorLow valueDescriptorSite pvSite pvPc pvFragment
  kvStart sharedDescriptor pvElection electSite pvSrcRegs RoleShape pvCutCode pvWalkCut
  normalBeforeLaterEvent pvWalkEvent electTemplate electStateFrame secondOutputCommitLeader
  mmaCutStep sameLeader valuePackedIssues)

noncomputable section

/-- The observed, decoded V reply reaches every fragment of both actual PV groups. -/
theorem InitialValueReplyCursor.actualValueFragmentB {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec)
    (cursor : InitialValueReplyCursor l X commit)
    (hWord : cursor.word = b32 (valueDescriptorLow l 1))
    (stage : Fin 2) (fragment : Fin 8) :
    ∃ issue dst operands accum mask,
      InitialValueFragment X issue cursor.steady stage fragment dst operands accum mask ∧
      operands.b = sharedDescriptor (kvStart l 1 + pvFragment fragment) 16384 ∧
      TraceBefore X (commit.1,cursor.index) issue ∧ TraceBefore X issue commit := by
  obtain ⟨g,j⟩ := commit
  obtain ⟨steady,index,reply,ok,state,visits,hSend,hBeforeCommit,hCursorAt,hCursorWalk⟩ :=
    cursor
  change reply = b32 (valueDescriptorLow l 1) at hWord
  let target : Event := ⟨2646,.tc (.commit spec)⟩
  have hCommitGet : X.get (g,j) = some target := hCommit.decoded
  let pos := index+1
  have hPos : pos ≤ j := Nat.succ_le_of_lt hBeforeCommit.2.1
  have hTarget : target ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := j-pos)
    rwa [List.getElem?_drop, Nat.add_sub_of_le hPos]
  let block := firstPvBlock steady stage
  let election := pvElection block
  let electPc := (electSite election).pc
  let start := (valueDescriptorSite steady).prepare+9
  let packPc := pvPc block 0-4
  let low := (valueDescriptorSite steady).output
  let word := b32 (valueDescriptorLow l 1)
  let F := [(low,word),(1062,b32 12)]
  have hPcBounds : 2145 ≤ start ∧ start ≤ electPc ∧ electPc < packPc ∧
      packPc < pvPc block fragment ∧ pvPc block fragment < 2646 := by
    cases steady <;> fin_cases stage <;> fin_cases fragment <;> decide
  have hSrc : (pvSrcRegs block).2.2 = low := by
    cases steady <;> fin_cases stage <;> decide
  have hGuard : (electSite election).pred = (pvSite block).guard := by
    cases steady <;> fin_cases stage <;> decide
  have hs := hCursorAt
  rw [hWord] at hs
  have hs' : At state start F := hs
  have hRole : RoleShape state ∧ state.regs 1062 = some (b32 12) :=
    ⟨⟨hs'.2.1.symm ▸ Nat.zero_le _, hs'.2.2.1, fun _ => hs'.2.1⟩, hs'.2.2.2.2.2.1⟩
  have hAudit : ((kernel.code.drop start).take (electPc-start)).all
      (pvCutCode start electPc (F.map Prod.fst)) = true := by
    cases steady <;> fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨s,pre,tail,post,hSplit,hsPc,hsShape,hsRegs,hsWalk,hsTarget,hBefore⟩ :=
    pvWalkCut (show 1907 ≤ start by omega) (show electPc < 2768 by omega) hAudit
      hCursorWalk (by rw [hs'.1]; exact ⟨le_rfl,hPcBounds.2.1⟩) hRole hs'.2.2.2.2 hTarget
      (show electPc ≤ 2646 by omega)
  have hLate : s.pc < target.pc := by rw [hsPc]; show electPc < 2646; omega
  have ht : At s electPc F :=
    ⟨hsPc,hsShape.1.2.2 (by omega),hsShape.1.2.1,
      normalBeforeLaterEvent hsWalk hsTarget hLate,hsRegs⟩
  obtain ⟨afterElect,ev,eTail,eVisits,hE,hFire,hEStep,hAfter,hLater⟩ :=
    pvWalkEvent hsWalk (electTemplate election ht) hsTarget hLate
  obtain ⟨inst,leader,rfl,hNew⟩ := hFire
  have hNe : (⟨s.pc,.elect (2^32-1) inst leader⟩ : Event) ≠ target := by
    intro h
    cases congrArg Event.kind h
  obtain ⟨hGet,hElectEarlier,hRest⟩ := nextBeforeRecorded hCommitGet hPos
    (hSplit.trans (by rw [hE])) (fun h => by
      have he := hBefore target h
      change 2646 < electPc at he
      omega) hNe
  obtain ⟨_,_,finalLeader,hElect,hSelected⟩ := secondOutputCommitLeader hp hX hCommitGet
  have hg := event_thread_lt hX hCommitGet
  have hEq := sameLeader hX (show SameWarp l g g from ⟨⟨hg,hg,rfl⟩,rfl⟩) hGet hElect
  have hLead : (laneOf l g == leader) = true := beq_iff_eq.mpr (hSelected.trans hEq.symm)
  obtain rfl := Option.some.inj hNew
  have hFramePred : ∀ pair ∈ F, pair.1 ≠ (electSite election).pred := by
    cases steady <;> fin_cases stage <;> simp [F,low,block,election,firstPvBlock,
      valueDescriptorSite,pvElection,electSite]
  have hFrameData : ∀ pair ∈ F, pair.1 ∉ (electSite election).result.toList := by
    cases steady <;> fin_cases stage <;> simp [election,block,firstPvBlock,pvElection,electSite]
  have hAt := electStateFrame (l := l) (g := g) election ht leader hFramePred hFrameData
  rw [hLead,hGuard] at hAt
  have hShape := (mmaCutStep (by omega) (by omega) (.inr ⟨_,rfl,hEStep⟩) hsShape).2
  let G := ((pvSite block).guard,.pred true) :: F
  have hPackAudit : ((kernel.code.drop (electPc+1)).take (packPc-(electPc+1))).all
      (pvCutCode (electPc+1) packPc (G.map Prod.fst)) = true := by
    cases steady <;> fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v,gap,pTail,pVisits,hParts,hPc,hPShape,hPRegs,hPWalk,hPTarget,hGap⟩ :=
    pvWalkCut (show 1907 ≤ electPc+1 by omega) (show packPc < 2768 by omega)
      hPackAudit hAfter (by
        have hAtPc : _ = electPc+1 := hAt.1
        rw [hAtPc]
        omega) hShape (F := G) hAt.2.2.2.2 hLater (show packPc ≤ 2646 by omega)
  have hpAt : At v packPc
      [((pvSrcRegs block).2.2,word),(1062,b32 12),((pvSite block).guard,.pred true)] := by
    rw [hSrc]
    exact ⟨hPc,hPShape.1.2.2 (by omega),hPShape.1.2.1,
      normalBeforeLaterEvent hPWalk hPTarget (by rw [hPc]; show packPc < 2646; omega),
      hPRegs.2.1,hPRegs.2.2.1,hPRegs.1,trivial⟩
  have hFragments : ∀ step : Fin 8, pvPc block step < target.pc := by
    intro step
    change pvPc block step < 2646
    cases steady <;> fin_cases stage <;> fin_cases step <;> decide
  obtain ⟨p,after,dst,operands,accum,mask,hMma,hB,_,hMmaPre⟩ :=
    valuePackedIssues hp block 1 hpAt hPWalk hPTarget hFragments fragment
  let issueEvent : Event := ⟨pvPc block fragment,.tc (.mma dst operands accum mask)⟩
  have hSuffix : (X.tr g).drop ((pos+pre.length)+1) = (gap++p) ++ issueEvent :: after := by
    simp [hRest,hParts,hMma,List.append_assoc,issueEvent]
  obtain ⟨hMmaGet,hMmaBefore,_⟩ := nextBeforeRecorded hCommitGet
    (show (pos+pre.length)+1 ≤ j by omega) hSuffix (fun hm => by
      rcases List.mem_append.mp hm with hm | hm
      · have h := hGap target hm
        change 2646 < packPc at h
        omega
      · exact (Nat.not_lt_of_ge (hFragments fragment).le) (hMmaPre target hm))
    (fun hEq => by
      have hh : pvPc block fragment = target.pc := congrArg Event.pc hEq
      exact Nat.ne_of_lt (hFragments fragment) hh)
  exact ⟨_,dst,operands,accum,mask,hMmaGet,hB,
    ⟨rfl,by dsimp [pos]; omega,(List.getElem?_eq_some_iff.mp hMmaGet).1⟩,
    ⟨rfl,hMmaBefore,(List.getElem?_eq_some_iff.mp hCommitGet).1⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
