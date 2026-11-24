-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
import all Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
import Lemmas.Order.ElectSiteOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem fullMember (l : Launch) (g : Nat) : electMember (2^32-1) (laneOf l g) := by
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  exact ⟨hLane,by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hLane⟩

/-- An actual score commit bounds the number of successful prerequisite
probability acquires on every MMA lane of its CTA. -/
theorem scoreOrdinalLePeerProbabilityCount {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {e : EvId} {cta g : Nat} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hIssue : ScoreCommit l X e cta stage spec rank) (packet : Fin 2)
    (hg : g < l.threads) (hCta : g/l.block = cta) (hWarp : warpIndex l g = 12) :
    scoreCommitOrdinal l X cta stage e ≤
      okPolls (probabilityObject l cta stage packet) (X.tr g) := by
  obtain ⟨issuer,index⟩ := e
  by_cases hPos : 0 < scoreCommitOrdinal l X cta stage (issuer,index)
  · let slot := scoreSlot stage packet
    let obj := probabilityObject l cta stage packet
    obtain ⟨block,hStage,hRepeat,hGet⟩ := positiveScoreCommitRepeats hp hX hIssue hPos
    obtain ⟨_,inst,leader,hElect,_⟩ := scoreCommitLeader hp hX block hGet
    have hSite : (electSite (commitElection (qkCommitSite block))).pc =
        probabilityScoreElection slot := by
      dsimp only [slot]
      fin_cases block <;> fin_cases stage <;> fin_cases packet <;> first | decide | contradiction
    rw [hSite] at hElect
    have hActor := scoreCommitActor hp hX hIssue
    have hSame : SameWarp l issuer g :=
      ⟨⟨event_thread_lt hX hGet,hg,hActor.1.trans hCta.symm⟩,hActor.2.1.trans hWarp.symm⟩
    obtain ⟨j,hPeer⟩ := ElectOrd.partner hX hSame hElect (fullMember l g)
    have hRank := ElectOrd.siteOrdinal_eq hX (· == probabilityScoreElection slot) hSame
      (fun _ _ _ _ _ _ he => (Thread.actualFullElectionMask hX he).symm ▸ fullMember l g)
      (fun _ _ _ _ _ _ he => (Thread.actualFullElectionMask hX he).symm ▸ fullMember l issuer) hPeer
    obtain ⟨src,dst,mask,mask',inst',a,b,hSrc,hDst⟩ := hPeer
    have hSrcPc := congrArg Event.pc (Option.some.inj (hSrc.symm.trans hElect))
    change src = probabilityScoreElection slot at hSrcPc
    have hDstPc := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ hSrc hDst hSame).1
    rw [← hDstPc,hSrcPc] at hDst
    obtain ⟨k,_,loc,q,acq,sc,hWait,hOrdinal⟩ := probabilityWaitAtScoreElection hp hX slot hDst
    let mark (ev : Event) : Bool :=
      match ev.kind with
      | .wait _ _ true _ _ => ev.pc == probabilityPc slot false
      | _ => false
    have hAddr : probabilityPc slot false ∈ [2141,2145,2210,2297,2335,2419,2450,
        2548,2586,2595,2626] ∧
        fixedMmaWaitOffset (probabilityPc slot false) = 96+8*stage.val+16*packet.val := by
      dsimp only [slot]
      fin_cases stage <;> fin_cases packet <;> decide
    have hLoc := mmaFixedWaitAddress hp hX hWait hAddr.1
    rw [hCta,hAddr.2] at hLoc
    change loc = obj at hLoc
    rw [hLoc] at hWait
    have hCount : ((X.tr g).take k).countP mark ≤ okPolls obj ((X.tr g).take k) := by
      apply List.countP_mono_left
      intro ev hMem hm
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hMem)
      obtain ⟨pc,kind⟩ := ev
      cases kind <;> try cases hm
      case wait other pq ok pa ps =>
        cases ok <;> try cases hm
        have hPc : pc = probabilityPc slot false := beq_iff_eq.mp hm
        subst pc
        have hOther := mmaFixedWaitAddress hp hX (g := g) (index := i) hi hAddr.1
        rw [hCta,hAddr.2] at hOther
        change other = obj at hOther
        simp [okPoll,sourceWaitSuccess,hOther]
    have hAdd := MbarRing.Poll.okPoll_get hWait
    have hMono := MbarRing.Poll.okPolls_mono obj (X.tr g)
      (show k+1 ≤ (X.tr g).length from len_of_get hWait)
    change ((X.tr g).take k).countP mark = _ at hOrdinal
    change okPolls obj ((X.tr g).take (k+1)) = okPolls obj ((X.tr g).take k)+1 at hAdd
    have hBudget := scoreBudgetAtElection hp hX stage packet (g := issuer) (j := index) (cta := cta)
    change scoreCommitOrdinal l X cta stage (issuer,index) ≤
      1+ElectOrd.siteOrdinal (· == probabilityScoreElection slot) X issuer (index-1) at hBudget
    change scoreCommitOrdinal l X cta stage (issuer,index) ≤ okPolls obj (X.tr g)
    rw [List.take_length] at hMono
    omega
  · omega

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
