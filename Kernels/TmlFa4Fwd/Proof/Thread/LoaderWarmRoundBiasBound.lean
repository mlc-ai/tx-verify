-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasOrder
import all Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderBiasGuard
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Flow.ContinuingEvent
import Lemmas.Order.ElectSiteOrdinal
import Lemmas.Protocol.ElectCount
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- A lane of warp 14 that waits at a warm Bias-empty poll and later issues a Bias box
elects itself at the box's selecting election in between. -/
theorem issuerElectionAfterWait {l : Launch} {X : Execution}
    {g pc shuffles votes li j : Nat} {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g pc F shuffles votes ends)
    (hli : li < 32) (hPc : 174 ≤ pc ∧ pc ≤ 1901)
    (hRegs : Holds (cur.state li).regs [(2535,b32 l.sharedBase),(1062,b32 14)])
    (site : Fin 10) (hAfter : pc < (biasTensorSelector site).elect)
    {address : Nat} {spec : TensorCopy.Spec}
    (he : X.get (warpLane l g li,j) =
      some ⟨(biasTensorSelector site).issue,.tensorIssue address spec⟩)
    (hj : cur.pos li ≤ j) :
    ∃ q, cur.pos li ≤ q ∧ q < j ∧ ∃ inst,
      X.Elect (warpLane l g li,q) (biasTensorSelector site).elect (2^32-1) inst
        (laneOf l (warpLane l g li)) := by
  let ti := warpLane l g li
  let sel := biasTensorSelector site
  have hR : 174 ≤ sel.elect ∧ sel.elect < sel.branch ∧
      sel.branch < sel.issue ∧ sel.issue < 1901 := tensorSelectorRange site
  have hAt := cur.checkpoint li hli
  have hIn : (⟨sel.issue,.tensorIssue address spec⟩ : Event) ∈ (X.tr ti).drop (cur.pos li) := by
    apply List.mem_of_getElem? (i := j-cur.pos li)
    rw [List.getElem?_drop,Nat.add_sub_of_le hj]
    exact he
  have hRun := (cur.continuation li hli).after_local_nonempty (cur.localSteps li hli)
    (List.ne_nil_of_mem hIn)
  obtain ⟨vs,hWalk⟩ := Mma.walkFromRun hRun
  have hDrop : ((X.tr ti).drop (cur.pos li))[j-cur.pos li]? =
      some ⟨sel.issue,.tensorIssue address spec⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hj]
    exact he
  have hStart : BeforeTensorSelection site l ti (cur.state li) := by
    intro h
    have := h.1
    rw [hAt.1] at this
    omega
  obtain ⟨k,hk,e,hE,⟨inst,rfl⟩⟩ := loaderEventPrecededBy (warp := 0) hWalk
    (by rw [hAt.1]; omega) (ringShapeOfAt hAt) hRegs hStart hDrop hR.2.2.2
    (fun {t} hb hPc => by
      change t.pc = sel.issue at hPc
      have hIn : selectorInterior sel t.pc := ⟨by omega,hPc.le⟩
      obtain ⟨u,hPath,hu⟩ := hb hIn
      rcases Relation.ReflTransGen.cases_head hPath with rfl | ⟨first,hTau,_⟩
      · change t.pc = sel.issue+1 at hu
        omega
      have hCore : Tau kernel [] l ti t first := by
        unfold Tau at hTau ⊢
        rwa [← loaderOutCore (by omega) (by omega)]
      have hc := inputSiteCode sel.input
      dsimp only at hc
      change t.pc = (inputSite sel.input).pc at hPc
      rw [← hPc] at hc
      exact tau_core_not_event hc rfl hCore)
    (fun hlo hhi hShape _ hBefore hStep hNo =>
      beforeTensorSelectionStep site hlo hhi hShape hBefore hStep hNo)
  refine ⟨cur.pos li+k,by omega,by omega,inst,?_⟩
  change (X.tr ti)[cur.pos li+k]? = _
  rw [List.getElem?_drop] at hE
  exact hE

private theorem fullMember' {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc mask inst lead : Nat}
    (h : X.Elect i pc mask inst lead) (peer : Nat) : electMember mask (laneOf l peer) := by
  rw [Thread.actualFullElectionMask hX h]
  have hLane : laneOf l peer < 32 := Nat.mod_lt _ (by decide)
  refine ⟨hLane,?_⟩
  rw [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
  exact hLane

private theorem waitBeforeBox (stage half : Fin 2) :
    (warmBiasEmptyWait stage).pc < warmBiasSite (warmBiasBoxSite stage half) ∧
    (if stage = 0 then 1149 else 1178) ≤ warmBiasIssueSite stage half ∧
    warmBiasIssueSite stage half ≤ 1239 ∧
    (warmBiasEmptyWait stage).pc < (if stage = 0 then 1149 else 1178) := by
  fin_cases stage <;> fin_cases half <;> decide

set_option maxRecDepth 4096 in
/-- While a lane of warp 14 is stalled at a warm Bias-empty poll of round `round`, no Bias
box of that stage in the CTA has a generation above `round`. A later box needs a full-warp
election that includes the stalled lane. -/
theorem warmBiasOrdinalsAtMost {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round shuffles votes : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hRound : round < warmRounds p l g batch) (stage : Fin 2)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmBiasEmptyWait stage).pc F shuffles votes ends)
    (hRank : shuffles = primingSearchShuffleCount batch+96+64*round)
    (hRegs : ∀ lane < 32, Holds (cur.state lane).regs [(2535,b32 l.sharedBase),(1062,b32 14)])
    (hLower : ∀ lane < 32, ∀ k, round ≤ warmBiasSiteCount X (warpLane l g lane) (cur.pos lane) k)
    {lane : Nat} (hl : lane < 32)
    (failed : ∀ e ∈ (X.tr (warpLane l g lane)).drop (cur.pos lane),
      ∃ loc, e.kind = .wait loc (round%2) false true .cta) :
    ∀ issue half spec, issue.1/l.block = g/l.block → BiasSubbox p l X issue stage half spec →
      biasTensorOrdinal l X stage half issue ≤ round := by
  intro issue half spec owner box
  obtain ⟨issuer,j⟩ := issue
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hRole : 14 ≤ warpIndex l g := by omega
  have hWarp : warpIndex l issuer = 14 := biasTensorActorWarp hp hX box
  have hSameG : SameWarp l issuer g :=
    ⟨⟨event_thread_lt hX box.1.choose_spec,hg,owner⟩,hWarp.trans hw.symm⟩
  have hPeer : SameWarp l issuer (warpLane l g lane) :=
    Step.sameWarp_trans hSameG (Step.sameWarp_lane hBlock hg hl).1
  let li := laneOf l issuer
  have hli : li < 32 := Nat.mod_lt _ (by decide)
  have hIssuer : warpLane l g li = issuer := Step.warpLane_of_sameWarp (sameWarp_symm hSameG)
  have hWaitPc : 174 ≤ (warmBiasEmptyWait stage).pc ∧ (warmBiasEmptyWait stage).pc ≤ 1901 := by
    fin_cases stage <;> decide
  have hPosRank (q : Nat) (hq : q < 32) :
      ((X.tr (warpLane l g q)).take (cur.pos q)).countP Execution.isShfl =
        primingSearchShuffleCount batch+96+64*round :=
    (cur.ordinals.shfl q hq).trans hRank
  have hW : round+1 ≤ warmRounds p l g batch := hRound
  -- The stalled lane's own trace ends in failed polls.
  have hStalled (k' : Nat) (pc : Nat) (mask inst lead : Nat)
      (h : X.Elect ((warpLane l g lane),k') pc mask inst lead) : k' < cur.pos lane := by
    by_contra! hLate
    have hMem : (⟨pc,.elect mask inst lead⟩ : Event) ∈
        (X.tr (warpLane l g lane)).drop (cur.pos lane) := by
      apply List.mem_of_getElem? (i := k'-cur.pos lane)
      rw [List.getElem?_drop,Nat.add_sub_of_le hLate]
      exact h
    obtain ⟨_,hBad⟩ := failed _ hMem
    cases hBad
  -- Some election of the issuer after its wait, together with its partner in the stalled lane.
  have hPartner (site : Fin 10) (hAfter : (warmBiasEmptyWait stage).pc <
      (biasTensorSelector site).elect) {address : Nat}
      (he : X.get (issuer,j) =
        some ⟨(biasTensorSelector site).issue,.tensorIssue address spec⟩)
      (hj : cur.pos li ≤ j) :
      ∃ q k' inst mask' inst' lead', cur.pos li ≤ q ∧
        X.Elect (issuer,q) (biasTensorSelector site).elect (2^32-1) inst (laneOf l issuer) ∧
        X.Elect ((warpLane l g lane),k') (biasTensorSelector site).elect mask' inst' lead' ∧
        k' < cur.pos lane ∧
        ElectOrd.siteOrdinal (fun pc => pc == (biasTensorSelector site).elect) X issuer q =
          ElectOrd.siteOrdinal (fun pc => pc == (biasTensorSelector site).elect) X
            (warpLane l g lane) k' := by
    rw [← hIssuer] at he
    obtain ⟨q,hq,_,inst,hElect⟩ := issuerElectionAfterWait cur hli hWaitPc (hRegs li hli) site
      hAfter he hj
    rw [hIssuer] at hElect
    obtain ⟨k',src,dst,mask,mask',ord,lead,lead',orig,partner⟩ :=
      ElectOrd.partner hX hPeer hElect (electMember_full l (warpLane l g lane))
    have hSrc : src = (biasTensorSelector site).elect :=
      congrArg Event.pc (Option.some.inj (orig.symm.trans hElect))
    have hDst : dst = (biasTensorSelector site).elect :=
      (hX.elect.2.1 _ _ _ _ _ _ _ _ _ orig partner hPeer).1.symm.trans hSrc
    rw [hDst] at partner
    have hEq := ElectOrd.siteOrdinal_eq hX (fun pc => pc == (biasTensorSelector site).elect)
      hPeer (fun _ _ _ _ _ _ h => fullMember' hX h _) (fun _ _ _ _ _ _ h => fullMember' hX h _)
      ⟨_,_,_,_,_,_,_,orig,partner⟩
    exact ⟨q,k',inst,mask',ord,lead',hq,hElect,partner,hStalled _ _ _ _ _ partner,hEq⟩
  obtain ⟨site,hStage,hHalf,he⟩ := biasTensorSelectorOfSubbox hp hX box
  have hClass : (biasTensorSelector site).input = firstBiasIssueSite stage half ∨
      ((biasTensorSelector site).input = warmBiasInputSite stage half ∧
        (biasTensorSelector site).elect = warmBiasSite (warmBiasBoxSite stage half)) ∨
      (1353 ≤ (biasTensorSelector site).issue ∧ 1353 ≤ (biasTensorSelector site).elect ∧
        stage = 0) := by
    fin_cases site <;> fin_cases stage <;> fin_cases half <;> first | contradiction | decide
  rcases hClass with hPrime | ⟨hInput,hElectSite⟩ | ⟨hLateIssue,hLateElect,hStage0⟩
  · have hz := biasPrimingOrdinalZero hp hX stage half (g := issuer) (j := j) (spec := spec)
      (by simpa only [BiasTensorSelector.issue,hPrime] using he)
    rw [hz]
    exact Nat.zero_le _
  · -- A warm box of an earlier round has generation at most `round`.
    have he' : X.get (issuer,j) = some ⟨warmBiasIssueSite stage half,
        .tensorIssue p.biasMapAddress spec⟩ := by
      simpa only [BiasTensorSelector.issue,hInput,warmBiasInputSite_pc] using he
    have hCuQ := (hFrame.metadataProtected hp).1
    obtain ⟨b,hB,hL,hH,round',_,hRankJ,hOrd⟩ :=
      warmBiasOrdinalExact hp hX hFrame hCuQ stage half box he'
    change issuer/l.block = g/l.block at owner
    rw [owner] at hL hH
    have hCTA : g/l.block < tilePrefix p p.batch*p.heads :=
      hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
    obtain ⟨_,_,uniq⟩ := tileBatch_existsUnique p hCTA
    have hEq : b = batch := (uniq b ⟨hB,hL,hH⟩).trans (uniq batch ⟨hb,hLo,hHi⟩).symm
    subst b
    rw [hOrd]
    by_contra! hNot
    have hBox := waitBeforeBox stage half
    by_cases hj : j < cur.pos li
    · have hMono := countP_take_mono Execution.isShfl (X.tr issuer) hj.le
      have hI := hPosRank li hli
      rw [hIssuer] at hI
      have hSame : round' = round := by omega
      have hlo : (if stage = 0 then 1149 else 1178) = 1149 ∨
          (if stage = 0 then 1149 else 1178) = 1178 := by fin_cases stage <;> decide
      have hTarget := warpPrefixReach cur li hli
      rw [hIssuer] at hTarget
      exact noReturnAfterEvent _ hlo he' ⟨hBox.2.1,hBox.2.2.1⟩ hj hTarget
        (by rw [(cur.checkpoint li hli).1]; exact hBox.2.2.2) (by omega)
    · obtain ⟨q,k',inst,mask',inst',lead',hq,hElect,hPart,hk',hEq⟩ :=
        hPartner site (by rw [hElectSite]; exact hBox.1) he (by omega)
      rw [hElectSite] at hEq hPart
      have hUpper := warmBiasSiteCountUpper hp hX hFrame hg hRole hb hl hLo hHi
        (warmBiasBoxSite stage half)
        (warpPrefixReach cur lane hl) (by rw [(cur.checkpoint lane hl).1]; exact hBox.1.le)
        (le_of_eq (hPosRank lane hl))
      have hLowI := hLower li hli (warmBiasBoxSite stage half)
      rw [hIssuer] at hLowI
      have hMonoI := countP_take_mono (ElectOrd.atSites (fun pc => pc ==
        warmBiasSite (warmBiasBoxSite stage half))) (X.tr issuer) hq
      have hSucc := countP_take_succ (p := ElectOrd.atSites (fun pc => pc ==
        warmBiasSite (warmBiasBoxSite stage half))) hPart warmBiasSite_atSites
      have hMonoT := countP_take_mono (ElectOrd.atSites (fun pc => pc ==
        warmBiasSite (warmBiasBoxSite stage half))) (X.tr (warpLane l g lane))
        (show k'+1 ≤ cur.pos lane by omega)
      unfold warmBiasSiteCount ElectOrd.siteOrdinal at hUpper hLowI
      unfold ElectOrd.siteOrdinal at hEq
      omega
  · -- A box after the warm rounds has a later shuffle rank than any stalled warm lane.
    exfalso
    have hLateRank (q : Nat) (hq : q < 32) {i : Nat} {e : Event}
        (h : X.get (warpLane l g q,i) = some e) (hPc : 1353 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :=
      lateLoaderEventRank hp hX hFrame hg hRole hb hq hLo hHi hTrips h hPc hSafe
    by_cases hj : j < cur.pos li
    · have hMono := countP_take_mono Execution.isShfl (X.tr issuer) hj.le
      have hI := hPosRank li hli
      rw [hIssuer] at hI
      have he2 : X.get (warpLane l g li,j) = some ⟨(biasTensorSelector site).issue,
          .tensorIssue p.biasMapAddress spec⟩ := by rw [hIssuer]; exact he
      have hJ := hLateRank li hli he2 hLateIssue (by intro _ h; cases h)
      rw [hIssuer] at hJ
      omega
    · obtain ⟨_,k',_,_,_,_,_,_,hPart,hk',_⟩ :=
        hPartner site (by have := waitBeforeBox stage half; subst hStage0; omega) he (by omega)
      have hK := hLateRank lane hl hPart hLateElect (by intro _ h; cases h)
      have hMono := countP_take_mono Execution.isShfl (X.tr (warpLane l g lane)) hk'.le
      have hT := hPosRank lane hl
      omega

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
