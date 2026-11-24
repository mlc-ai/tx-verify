-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderWarmRoundBiasReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTailBias
import all Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Protocol.ElectCount

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.Proof PTX.MBarrier PTX.EventFrame Prologue Epilogue Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Loader

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

set_option maxRecDepth 4096 in
/-- While a lane of warp 14 is stalled at the tail Bias-empty poll, every stage-zero Bias box
of the CTA belongs to the priming packet or to a warm round. A tail box would need an
election at a pc that the stalled lane cannot have passed. -/
theorem tailBiasOrdinalsAtMost (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 1361 F shuffles votes ends)
    (hRegs : ∀ lane < 32, Holds (cur.state lane).regs [(2535,b32 l.sharedBase),(1062,b32 14)])
    {lane : Nat} (hl : lane < 32)
    (failed : ∀ e ∈ (X.tr (warpLane l g lane)).drop (cur.pos lane),
      ∃ loc parity, e.kind = .wait loc parity false true .cta) :
    ∀ issue half spec, issue.1/l.block = g/l.block → BiasSubbox p l X issue 0 half spec →
      biasTensorOrdinal l X 0 half issue ≤ warmRounds p l g batch := by
  intro issue half spec owner box
  obtain ⟨issuer,j⟩ := issue
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hWarp : warpIndex l issuer = 14 := biasTensorActorWarp hp hX box
  have hSameG : SameWarp l issuer g :=
    ⟨⟨event_thread_lt hX box.1.choose_spec,hg,owner⟩,hWarp.trans hw.symm⟩
  have hPeer : SameWarp l issuer (warpLane l g lane) :=
    Step.sameWarp_trans hSameG (Step.sameWarp_lane hBlock hg hl).1
  let li := laneOf l issuer
  have hli : li < 32 := Nat.mod_lt _ (by decide)
  have hIssuer : warpLane l g li = issuer := Step.warpLane_of_sameWarp (sameWarp_symm hSameG)
  have hFloor : TailFloor 1365 := .inl rfl
  have hAbove {t : Nat} {e : Event} (hPc : 1365 ≤ e.pc ∧ e.pc < 1901) {s u : TState}
      (h : EStep kernel Assumptions.all l t s e (some u)) : 1365 ≤ u.pc := by
    have hs : s.pc = e.pc := (estep_source_pc h).symm
    have h' : EStep kernel [] l t s e (some u) := by
      obtain ⟨tmpl,hO,hF⟩ := h
      exact ⟨tmpl,by rwa [← loaderOutCore (by omega) (by omega)],hF⟩
    have := estep_return_pc h' (fun _ _ _ h => execLocal_frame h)
    omega
  obtain ⟨site,hStage,hHalf,he⟩ := biasTensorSelectorOfSubbox hp hX box
  have hClass : (biasTensorSelector site).input = firstBiasIssueSite 0 half ∨
      (biasTensorSelector site).input = warmBiasInputSite 0 half ∨
      (1365 ≤ (biasTensorSelector site).issue ∧ (biasTensorSelector site).issue < 1901 ∧
        1365 ≤ (biasTensorSelector site).elect ∧ (biasTensorSelector site).elect < 1901) := by
    fin_cases site <;> fin_cases half <;> first | contradiction | decide
  rcases hClass with hPrime | hInput | ⟨hLateIssue,hIssueHi,hLateElect,hElectHi⟩
  · have hz := biasPrimingOrdinalZero hp hX 0 half (g := issuer) (j := j) (spec := spec)
      (by simpa only [BiasTensorSelector.issue,hPrime] using he)
    rw [hz]
    exact Nat.zero_le _
  · have he' : X.get (issuer,j) = some ⟨warmBiasIssueSite 0 half,
        .tensorIssue p.biasMapAddress spec⟩ := by
      simpa only [BiasTensorSelector.issue,hInput,warmBiasInputSite_pc] using he
    obtain ⟨b,hB,hL,hH,round',hRound',_,hOrd⟩ :=
      warmBiasOrdinalExact hp hX hFrame (hFrame.metadataProtected hp).1 0 half box he'
    change issuer/l.block = g/l.block at owner
    rw [owner] at hL hH hRound'
    have hCTA : g/l.block < tilePrefix p p.batch*p.heads :=
      hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
    obtain ⟨_,_,uniq⟩ := tileBatch_existsUnique p hCTA
    have hEq : b = batch := (uniq b ⟨hB,hL,hH⟩).trans (uniq batch ⟨hb,hLo,hHi⟩).symm
    subst b
    rw [hOrd]
    unfold warmRounds
    omega
  · exfalso
    by_cases hj : j < cur.pos li
    · have hTarget := warpPrefixReach cur li hli
      rw [hIssuer] at hTarget
      exact noReturnBelowTailFloor hFloor he hj (hAbove ⟨hLateIssue,hIssueHi⟩) hTarget
        (by rw [(cur.checkpoint li hli).1]; decide)
    · rw [← hIssuer] at he
      obtain ⟨q,_,_,inst,hElect⟩ := issuerElectionAfterWait cur hli (by decide) (hRegs li hli)
        site (by omega) he (by omega)
      rw [hIssuer] at hElect
      obtain ⟨k',src,dst,mask,mask',ord,lead,lead',orig,partner⟩ :=
        ElectOrd.partner hX hPeer hElect (electMember_full l (warpLane l g lane))
      have hSrc : src = (biasTensorSelector site).elect :=
        congrArg Event.pc (Option.some.inj (orig.symm.trans hElect))
      have hDst : dst = (biasTensorSelector site).elect :=
        (hX.elect.2.1 _ _ _ _ _ _ _ _ _ orig partner hPeer).1.symm.trans hSrc
      rw [hDst] at partner
      have hk' : k' < cur.pos lane := by
        by_contra! hLate
        have hMem : (⟨(biasTensorSelector site).elect,.elect mask' ord lead'⟩ : Event) ∈
            (X.tr (warpLane l g lane)).drop (cur.pos lane) := by
          apply List.mem_of_getElem? (i := k'-cur.pos lane)
          rw [List.getElem?_drop,Nat.add_sub_of_le hLate]
          exact partner
        obtain ⟨_,_,hBad⟩ := failed _ hMem
        cases hBad
      exact noReturnBelowTailFloor hFloor partner hk' (hAbove ⟨hLateElect,hElectHi⟩)
        (warpPrefixReach cur lane hl) (by rw [(cur.checkpoint lane hl).1]; decide)

/-- The tail Bias-empty wait passes once softmax has released the warm generations of stage
zero. The phase cannot run ahead of the warm boxes while warp 14 is stalled. -/
theorem warmTailBiasReadyOfReleases (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hReleased : BiasEmptyReleased l X (g/l.block) 0 (warmRounds p l g batch+1)) :
    WarmTailBiasReady p l X g batch := by
  intro F shuffles votes ends cur _ hRegs lane hl failed
  obtain ⟨s,hs,hGe⟩ := hReleased
  have hLe := biasReusePhaseAtMost hp hX 0
    (tailBiasOrdinalsAtMost hp hX hFrame hg hw hb hLo hHi cur hRegs hl (fun e he => by
      obtain ⟨loc,h⟩ := failed e he
      exact ⟨loc,_,h⟩)) hs
  refine ⟨s,hs,?_⟩
  have hEq : s.phase = warmRounds p l g batch+1 := by omega
  rw [hEq]
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
