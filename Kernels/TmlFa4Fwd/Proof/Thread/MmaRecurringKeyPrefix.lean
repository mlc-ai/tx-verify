-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaRecurringKeyPack
public import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma
noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (stage : Fin 2) (frag : Fin 8)
    (use : Nat) {g : Nat} {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t (qkSetupPc (recurringKeyBlock stage) 0-2)
      [(2600,b32 (keyDescriptorLow l use)),(1062,b32 12)])
    (hw : Walk kernel Assumptions.all l g t es vs) {e : Event} (he : e ∈ es)
include hp stage frag use ht hw he

set_option maxRecDepth 100000 in
/-- Replay the actual key setup for the requested fragment and preserve the event suffix. -/
theorem recurringKeyPrefixRanged (hePc : e.pc = qkPc (recurringKeyBlock stage) + frag.val) :
    ∃ s rem post, s.pc = qkPc (recurringKeyBlock stage)+frag.val ∧
      s.regs (qkBReg (recurringKeyBlock stage)+frag.val) =
        some (b64 (sharedDescriptorWord (kvStart l use+qkFragment frag) 16)) ∧
      s.regs 2600 = some (b32 (keyDescriptorLow l use)) ∧
      (RoleShape s ∧ s.regs 1062 = some (b32 12)) ∧
      post.length < vs.length ∧ ∃ pre, es = pre ++ rem ∧
      Walk kernel Assumptions.all l g s rem post ∧ e ∈ rem ∧
      ∀ v ∈ pre, qkSetupPc (recurringKeyBlock stage) 0-2 ≤ v.pc ∧ v.pc < e.pc := by
  let block := recurringKeyBlock stage
  let seed := qkSetupPc block 0-2
  let start := initialKeyPackStart block frag
  let finish := qkSetupPc block frag+qkFirstSetupCount frag
  let issue := qkPc block+frag.val
  let G := recurringKeyPackFrame l block use
  let H := [(qkBReg block+frag.val,
    b64 (sharedDescriptorWord (kvStart l use+qkFragment frag) 16)),
    (1062,b32 12),(2600,b32 (keyDescriptorLow l use))]
  have hBounds : 1909 < seed ∧ seed+2 ≤ start ∧ start < finish ∧ finish < issue ∧
      issue < 2768 := by
    fin_cases stage <;> fin_cases frag <;> decide
  obtain ⟨b,hSeed,hB⟩ := recurringKeyPackSeed l g stage use t ht
  have hSeedStraight : ((kernel.code.drop seed).take (2-1)).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    fin_cases stage <;> kernel_rfl
  have hSeedReal := localRun (show 1904 ≤ seed by omega) (show seed+2 ≤ 2768 by omega)
    ht.1 hSeedStraight hSeed
  rcases advanceWalkLocals hSeedReal hw with hNil | ⟨bVisits,hBVisits,_,hbWalk⟩
  · rw [hNil] at he
    cases he
  have hbShape : RoleShape b ∧ b.regs 1062 = some (b32 12) :=
    ⟨⟨hB.2.1.symm ▸ Nat.zero_le _,hB.2.2.1,fun _ => hB.2.1⟩,hB.2.2.2.2.2.2.1⟩
  let begin := qkSetupPc block 0
  have hFrom : begin = seed+2 := by fin_cases stage <;> decide
  have hCheck' : ((kernel.code.drop begin).take (start-begin)).all
      (pvCutCode begin start (G.map Prod.fst)) = true := by
    fin_cases stage <;> fin_cases frag <;> kernel_rfl
  obtain ⟨c,pre,r,cVisits,hSplit,hcPc,hcShape,hcFacts,hcWalk,hcMem,hLen,hEarly⟩ :=
    pvWalkCutLengthRanged (show 1907 ≤ begin by omega) (show start < 2768 by omega) hCheck' hbWalk
      (by have hPc : b.pc = begin := hB.1; rw [hPc]; omega) hbShape hB.2.2.2.2
      he (by change e.pc = issue at hePc; omega)
  have hc : At c start G := ⟨hcPc,hcShape.1.2.2 (by omega),hcShape.1.2.1,
    normalBeforeLaterEvent hcWalk hcMem (by change e.pc = issue at hePc; omega),hcFacts⟩
  have hPackEntry :
      ∃ v skipped rest visits, r = skipped++rest ∧ visits.length ≤ cVisits.length ∧
        At v (finish-1) (recurringKeyWordFrame l block frag use) ∧
        Walk kernel Assumptions.all l g v rest visits ∧ e ∈ rest ∧
        ∀ q ∈ skipped, seed ≤ q.pc ∧ q.pc < issue := by
    by_cases hFrag : frag.val = 0
    · have hZero : frag = 0 := Fin.ext hFrag
      subst frag
      have hAt : start = finish-1 := by fin_cases stage <;> decide
      have hFacts : G = recurringKeyWordFrame l block 0 use := by
        simp [G,recurringKeyPackFrame,recurringKeyWordFrame,initialKeyLowReg,qkFragment]
      exact ⟨c,[],r,cVisits,rfl,le_rfl,hAt ▸ hFacts ▸ hc,hcWalk,hcMem,by simp⟩
    · obtain ⟨v,hAdd,hV⟩ := recurringKeyAddLocal hp g stage frag use hFrag c hc
      have hAddReal := localRun (show 1904 ≤ start by omega) (show start+1 ≤ 2768 by omega)
        hc.1 rfl hAdd
      rcases advanceWalkLocals hAddReal hcWalk with hNil | ⟨vVisits,hVVisits,_,hvWalk⟩
      · rw [hNil] at hcMem
        cases hcMem
      have hOne : start+1 ≤ finish-1 := by
        fin_cases stage <;> fin_cases frag <;> first | exact (hFrag rfl).elim | decide
      have hAudit : ((kernel.code.drop (start+1)).take (finish-1-(start+1))).all
          (pvCutCode (start+1) (finish-1) ((recurringKeyWordFrame l block frag use).map Prod.fst)) =
          true := by
        fin_cases stage <;> fin_cases frag <;> kernel_rfl
      have hVShape : RoleShape v ∧ v.regs 1062 = some (b32 12) :=
        ⟨⟨hV.2.1.symm ▸ Nat.zero_le _,hV.2.2.1,fun _ => hV.2.1⟩,hV.2.2.2.2.2.2.1⟩
      obtain ⟨w,skip,rest,visits,hRest,hPc,hSh,hF,hWalk,hM,hLength,hRange⟩ :=
        pvWalkCutLengthRanged (show 1907 ≤ start+1 by omega) (show finish-1 < 2768 by omega) hAudit
          hvWalk (by have hV' : v.pc = start+1 := hV.1; rw [hV']; omega)
          hVShape hV.2.2.2.2 hcMem (by change e.pc = issue at hePc; omega)
      have hw : At w (finish-1) (recurringKeyWordFrame l block frag use) :=
        ⟨hPc,hSh.1.2.2 (by omega),hSh.1.2.1,
          normalBeforeLaterEvent hWalk hM (by change e.pc = issue at hePc; omega),hF⟩
      refine ⟨w,skip,rest,visits,hRest,by omega,hw,hWalk,hM,?_⟩
      intro q hq
      have ⟨hL,hU⟩ := hRange q hq
      omega
  obtain ⟨pack,packPre,rPack,packVisits,hPackSplit,hPackLen,hPackAt,hPackWalk,hPMem,hPackRange⟩ :=
    hPackEntry
  obtain ⟨d,hPack,hd⟩ := recurringKeyPackFragment hp g stage frag use pack hPackAt
  have hPackReal := localRun (show 1904 ≤ finish-1 by omega) (show finish-1+1 ≤ 2768 by omega)
    hPackAt.1 rfl hPack
  rcases advanceWalkLocals hPackReal hPackWalk with hNil | ⟨dVisits,hDVisits,_,hdWalk⟩
  · rw [hNil] at hPMem
    cases hPMem
  have hdShape : RoleShape d ∧ d.regs 1062 = some (b32 12) :=
    ⟨⟨hd.2.1.symm ▸ Nat.zero_le _,hd.2.2.1,fun _ => hd.2.1⟩,hd.2.2.2.2.2.1⟩
  have hCheck'' : ((kernel.code.drop finish).take (issue-finish)).all
      (pvCutCode finish issue (H.map Prod.fst)) = true := by
    fin_cases stage <;> fin_cases frag <;> kernel_rfl
  obtain ⟨w,dPre,rem,post,hDPre,hwPc,hwShape,hwFacts,hwWalk,hwMem,hLength,hDoneRange⟩ :=
    pvWalkCutLengthRanged (show 1907 ≤ finish by omega) (show issue < 2768 by omega) hCheck'' hdWalk
      (by have hp : d.pc = finish := hd.1; rw [hp]; omega) hdShape hd.2.2.2.2
      hPMem (by change e.pc = issue at hePc; exact hePc.symm.le)
  refine ⟨w,rem,post,hwPc,hwFacts.1,hwFacts.2.2.1,hwShape,by omega,pre++packPre++dPre,?_,
    hwWalk,hwMem,?_⟩
  · simp [hSplit,hPackSplit,hDPre,List.append_assoc]
  · intro q hq
    rcases List.mem_append.mp hq with hLeft | hRest
    · rcases List.mem_append.mp hLeft with hPre | hLater
      · have ⟨hL,hU⟩ := hEarly q hPre
        change e.pc = issue at hePc
        change seed ≤ q.pc ∧ q.pc < e.pc
        omega
      · exact hePc.symm ▸ hPackRange q hLater
    · have ⟨hL,hU⟩ := hDoneRange q hRest
      change e.pc = issue at hePc
      change seed ≤ q.pc ∧ q.pc < e.pc
      omega

end
end PTX.Kernels.TmlFa4Fwd.Thread
