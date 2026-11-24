-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningSteadyRoots
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyDrain
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyOpeningLedger
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCohortPolls
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyTailEntry
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyTailPv
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalPvProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyTailAssembly
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyTailCommits
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalOutputProgress
import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheBroadcasts
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Proof.MmaValueDescriptorWord
import Kernels.TmlFa4Fwd.Flow.Code.Part035
import Kernels.TmlFa4Fwd.Flow.Code.Part040
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A fresh full-warp election issues its decoded commit; neither step polls. -/
theorem commitWarpFromFreshElectionWithPollCounts (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes base : Nat} (hg : g < l.threads)
    (site : Fin 12) {F : List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (electSite (commitElection site)).pc (fun _ => F)
      shuffles votes ends)
    (hFresh : ∀ lane < 32, ∀ j < cur.pos lane, ∀ mask inst leader,
      ¬ X.Elect (warpLane l g lane,j) (electSite (commitElection site)).pc mask inst leader)
    (hPred : ∀ pair ∈ F, pair.1 ≠ (electSite (commitElection site)).pred)
    (hAux : ∀ pair ∈ F, pair.1 ≠ (electSite (commitElection site)).pred+1)
    (hResult : ∀ pair ∈ F, pair.1 ∉ (electSite (commitElection site)).result.toList)
    (hBase : ((commitSite site).base,b32 base) ∈ F) (hWidth : base+(commitSite site).off < 2^32)
    (hAlign : (base+(commitSite site).off)%8 = 0) :
    ∃ next : SchedulerWarpReached l X g ((commitSite site).pc+1) (fun _ => F)
      shuffles votes ends,
    (∀ lane < 32, ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
      okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
    ∃ issuer index, SameWarp l g issuer ∧ X.get (issuer,index) =
      some ⟨(commitSite site).pc,.tc (.commit
        (commitSpec l issuer (base+(commitSite site).off)))⟩ ∧
      index+1 = next.pos (laneOf l issuer) := by
  let afterFrame := fun lane leader =>
    ((electSite (commitElection site)).pred,.pred (laneOf l (warpLane l g lane) == leader)) :: F
  obtain ⟨leader,elected,hElect⟩ := cur.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (cur.state lane) (commitElection site)) afterFrame
    hFresh (fun lane hl => electTemplate _ (cur.checkpoint lane hl))
    (fun lane hl k => electStateFrame _ (cur.checkpoint lane hl) k hPred hResult)
  obtain ⟨next,hCount,hEvent⟩ := commitWarpFromElectedWithPollCounts hp hMax hg site leader
    elected hAux hBase hWidth hAlign
  refine ⟨next,fun lane hl other => ?_,hEvent⟩
  obtain ⟨hi,inst,he⟩ := hElect lane hl
  rw [(hCount lane hl).2.2 other,hi]
  exact countP_take_succ_false he rfl

private theorem steadyTailQueryReturnWithPolls (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g visit shuffles votes : Nat}
    (hg : g < l.threads) (stage : Fin 2) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (electSite (commitElection (queryReturnSite stage))).pc
      (fun _ => steadyFrame l visit 1) shuffles votes ends) :
    ∃ next : SchedulerWarpReached l X g ((commitSite (queryReturnSite stage)).pc+1)
      (fun _ => steadyFrame l visit 1) shuffles votes ends,
    (∀ lane < 32, ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
      okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
    ∃ issuer index, SameWarp l g issuer ∧ X.Commit (issuer,index)
      (commitSpec l issuer (l.sharedBase+16+8*stage.val)) := by
  let site := queryReturnSite stage
  have hSite : (commitSite site).base = 2535 := by fin_cases stage <;> rfl
  have hOff : (commitSite site).off = 16+8*stage.val := by fin_cases stage <;> rfl
  have hWidth : l.sharedBase+(commitSite site).off < 2^32 := by
    rw [hOff]
    have := hp.shared.2.1
    have := stage.isLt
    omega
  have hAlign : (l.sharedBase+(commitSite site).off)%8 = 0 := by
    rw [hOff]
    have := hp.shared.1
    omega
  obtain ⟨tail,hPolls,issuer,index,hw,he,_⟩ :=
    commitWarpFromFreshElectionWithPollCounts hp hMax hg site cur
    (fun lane hl j hj mask inst leader he => noEarlierMmaElection _ (tailQueryReturnCode stage)
      (by fin_cases stage <;> (set_option maxRecDepth 15000 in kernel_rfl))
      (by fin_cases stage <;> kernel_rfl) (cur.checkpoint lane hl)
      (cur.recorded lane hl) (cur.localSteps lane hl) hj he)
    (by fin_cases stage <;>
      simp [steadyFrame,steadyPorts,site,queryReturnSite,commitElection,electSite])
    (by fin_cases stage <;>
      simp [steadyFrame,steadyPorts,site,queryReturnSite,commitElection,electSite])
    (by fin_cases stage <;>
      simp [steadyFrame,steadyPorts,site,queryReturnSite,commitElection,electSite])
    (by rw [hSite]; simp [steadyFrame,steadyPorts]) hWidth hAlign
  rw [hOff,← Nat.add_assoc] at he
  exact ⟨tail,hPolls,issuer,index,hw,_,he⟩

/-- Every lane of the warp has the same successful polls at two boundaries. -/
def SamePolls (l : Launch) (X : Execution) (g : Nat) (a b : Nat → Nat) : Prop :=
  ∀ lane < 32, ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (b lane)) =
    okPolls other ((X.tr (warpLane l g lane)).take (a lane))

theorem SamePolls.trans {l : Launch} {X : Execution} {g : Nat} {a b c : Nat → Nat}
    (hab : SamePolls l X g a b) (hbc : SamePolls l X g b c) : SamePolls l X g a c :=
  fun lane hl other => (hbc lane hl other).trans (hab lane hl other)

private theorem samePollsOfShuffle {l : Launch} {X : Execution} {g pc shuffles : Nat}
    {a b : Nat → Nat} {mode : ShflMode} {va : Nat → Value} {vb vc : Nat → Nat}
    (h : ∀ lane < 32, b lane = a lane+1 ∧ ∃ recv ok, X.get (warpLane l g lane,a lane) =
      some ⟨pc,.shfl mode (va lane) (vb lane) (vc lane) recv ok⟩ ∧
      X.ShflK (warpLane l g lane,a lane) shuffles) :
    SamePolls l X g a b := by
  intro lane hl other
  obtain ⟨hi,_,_,he,_⟩ := h lane hl
  rw [hi]
  exact countP_take_succ_false he rfl

private theorem samePollsOfElect {l : Launch} {X : Execution} {g site : Nat} {leader : Fin 32}
    {a b : Nat → Nat}
    (h : ∀ lane < 32, b lane = a lane+1 ∧
      ∃ inst, X.Elect (warpLane l g lane,a lane) site 4294967295 inst leader) :
    SamePolls l X g a b := by
  intro lane hl other
  obtain ⟨hi,_,he⟩ := h lane hl
  rw [hi]
  exact countP_take_succ_false he rfl

/-- The final body returns both query buffers and reaches the last V acquire without polling. -/
theorem steadyTailValueWaitWithPolls (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g visit shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2534 (fun _ => steadyFrame l visit 1) shuffles votes ends) :
    ∃ tail : SchedulerWarpReached l X g 2545 (fun _ => steadyTailValueFrame l visit)
        shuffles votes ends,
      SamePolls l X g cur.pos tail.pos ∧
      ∀ stage : Fin 2, ∃ issuer index, SameWarp l g issuer ∧
        X.Commit (issuer,index) (commitSpec l issuer (l.sharedBase+16+8*stage.val)) := by
  obtain ⟨second,h0,hFirst⟩ := steadyTailQueryReturnWithPolls hp hMax hg 0 cur
  obtain ⟨tail,h1,hSecond⟩ := steadyTailQueryReturnWithPolls hp hMax hg 1 second
  obtain ⟨wait,hPos⟩ := tail.advanceLocalWithPosition (fun lane hl =>
    steadyTailAddress hp (g := warpLane l g lane) (tail.checkpoint lane hl))
  refine ⟨wait,fun lane hl other => ?_,?_⟩
  · rw [hPos,h1 lane hl other,h0 lane hl other]
  · intro stage
    fin_cases stage
    · exact hFirst
    · exact hSecond

private theorem steadyFinalFirstPvElectWithPolls (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g visit shuffles votes : Nat}
    (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2551
      (fun _ => (6495,b32 (l.sharedBase+144))::steadyTailValueFrame l visit) shuffles votes ends) :
    ∃ leader : Fin 32, ∃ out : SchedulerWarpReached l X g 2563
      (fun lane => pvElectedFrame l g 2 (2*visit+1) (visit%2) (decide (0<visit))
        (steadyTerminalPvFrame l visit) lane leader) (shuffles+3) votes ends,
      SamePolls l X g cur.pos out.pos := by
  let use := 2*visit+1
  let low := valueDescriptorLow l use
  let D := firstTailSteadyDescriptors l visit
  obtain ⟨s,hs⟩ := cur.advanceLocalWithPosition (G := fun _ => D)
    (fun lane hl => firstTailSteadyDescriptorSetup hp _ (cur.checkpoint lane hl))
  obtain ⟨q,hq⟩ := s.consumeShuffleWithEvents (dst := 2611) hp hMax hg .idx (fun _ => b32 64)
    (fun _ => 0) (fun _ => 31) (by
      simp [D,firstTailSteadyDescriptors,steadyTailValueFrame,steadyFrame,steadyPorts]) (by
        intro lane hl
        exact valueProbabilityShuffle hp false ((s.checkpoint lane hl).mono
          ⟨holds_lookup (s.checkpoint lane hl).2.2.2.2 rfl,trivial⟩))
  obtain ⟨v,hv⟩ := q.consumeShuffleWithEvents (dst := 2612) hp hMax hg .idx
    (fun _ => b32 low) (fun _ => 0) (fun _ => 31) (by
      simp [D,firstTailSteadyDescriptors,steadyTailValueFrame,steadyFrame,steadyPorts]) (by
        intro lane hl
        exact valueDescriptorShuffle hp false use ((q.checkpoint lane hl).mono
          ⟨holds_lookup (q.checkpoint lane hl).2.2.2.2 rfl,trivial⟩))
  let F := (2627,b32 256) :: (2612,b32 low) :: (2611,b32 64) :: D
  obtain ⟨u,hu⟩ := v.advanceLocalWithPosition (pc' := 2561) (G := fun _ => F) (by
    intro lane hl
    have hAt := v.checkpoint lane hl
    let nextState := next (setReg (v.state lane) 2627 (b32 256))
    have hCore : run kernel [] l (warpLane l g lane) 1 (v.state lane) = some nextState := by
      apply run_local Flow.code_2560 rfl hAt
      rfl
    have hRun := localRun (by decide) (by decide) hAt.1 (by decide) hCore
    exact ⟨nextState,run_rtg hRun,hAt.set (by
      simp [D,firstTailSteadyDescriptors,steadyTailValueFrame,steadyFrame,steadyPorts])⟩)
  obtain ⟨w,hw⟩ := u.consumeShuffleWithEvents (dst := 2613) hp hMax hg .idx
    (fun _ => b32 256) (fun _ => 0) (fun _ => 31) (by
      simp [F,D,firstTailSteadyDescriptors,steadyTailValueFrame,steadyFrame,steadyPorts]) (by
        intro lane hl
        exact laneZeroBroadcast hp (by decide) ((u.checkpoint lane hl).mono
          ⟨holds_lookup (u.checkpoint lane hl).2.2.2.2 rfl,trivial⟩) Flow.code_2561)
  let E := pvEntryFacts l 2 use (visit%2) (decide (0<visit)) ++ steadyTerminalPvFrame l visit
  obtain ⟨c,hc⟩ := w.advanceLocalWithPosition (pc' := 2562) (G := fun _ => E) (by
    intro lane hl
    have ht := w.checkpoint lane hl
    let H := ht.2.2.2.2
    refine ⟨_,.refl,ht.mono ((holds_append ..).mpr ⟨?_,?_⟩)⟩
    · have hAcc : (if decide (0<visit) = true then 1 else 0) =
          (if 0<visit then 1 else 0) := by simp
      change Holds (w.state lane).regs
        [(2613,b32 256),(2611,b32 64),(2612,b32 low),
          (7206,b32 (if decide (0<visit) = true then 1 else 0)),
          (2614,b32 (l.sharedBase+112)),(7205,b32 (visit%2))]
      rw [hAcc]
      exact ⟨holds_lookup H rfl,holds_lookup H rfl,holds_lookup H rfl,holds_lookup H rfl,
        holds_lookup H rfl,holds_lookup H rfl,trivial⟩
    · exact ⟨holds_lookup H rfl,holds_lookup H rfl,holds_lookup H rfl,holds_lookup H rfl,
        holds_lookup H rfl,holds_lookup H rfl,holds_lookup H rfl,holds_lookup H rfl,trivial⟩)
  have hPred : ∀ pair ∈ E, pair.1 ≠ 9727 := by
    simp [E,pvEntryFacts,pvSrcRegs,pvSite,pvTailWait,waitSite,steadyTerminalPvFrame]
  obtain ⟨leader,out,hOut⟩ := c.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (c.state lane) 15)
    (fun lane leader => (9727,.pred (laneOf l (warpLane l g lane) == leader)) :: E)
    (fun lane hl _ hj _ _ _ he => noEarlierMmaElection 15 Flow.code_2562
      (by decide +kernel) (by decide +kernel) (c.checkpoint lane hl)
      (c.recorded lane hl) (c.localSteps lane hl) hj he)
    (fun lane hl => electTemplate 15 (c.checkpoint lane hl))
    (fun lane hl leader => electStateFrame 15 (c.checkpoint lane hl) leader hPred
      (by simp [electSite]))
  refine ⟨leader,out,?_⟩
  have hsq := samePollsOfShuffle hq
  have hqv := samePollsOfShuffle hv
  have huw := samePollsOfShuffle hw
  have hco := samePollsOfElect hOut
  intro lane hl other
  rw [hco lane hl other,hc,huw lane hl other,hu,hqv lane hl other,hsq lane hl other,hs]

private theorem secondBroadcastProgressWithPolls (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    (stage : Bool) {F : List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (secondBroadcast stage).1 (fun _ => F) shuffles votes ends)
    (hTmp : (secondBroadcast stage).2.1 ∉ F.map Prod.fst)
    (hDst : (secondBroadcast stage).2.2.1 ∉ F.map Prod.fst) :
    ∃ out : SchedulerWarpReached l X g ((secondBroadcast stage).1+2)
      (fun _ => ((secondBroadcast stage).2.2.1,b32 (secondBroadcast stage).2.2.2) ::
        ((secondBroadcast stage).2.1,b32 (secondBroadcast stage).2.2.2) :: F)
      (shuffles+1) votes ends,
      SamePolls l X g cur.pos out.pos := by
  let pc := (secondBroadcast stage).1
  let tmp := (secondBroadcast stage).2.1
  let dst := (secondBroadcast stage).2.2.1
  let value := (secondBroadcast stage).2.2.2
  have hCode : kernel.code[pc]? = some ⟨none,.move ⟨.scalar,.int .b 32,[some tmp],[.imm value]⟩⟩ ∧
      kernel.code[pc+1]? = some ⟨none,.warp ⟨.shfl .idx,some (.int .b 32),[some dst],
        [.reg tmp,.imm 0,.imm 31],some (.imm (-1))⟩⟩ := by
    cases stage
    · exact secondBroadcastCode false
    · exact secondBroadcastCode true
  have hLo : 1904 ≤ (secondBroadcast stage).1 := by cases stage <;> decide
  have hHi : (secondBroadcast stage).1+1 < 2768 := by cases stage <;> decide
  have hNe : (secondBroadcast stage).2.1 ≠ (secondBroadcast stage).2.2.1 := by
    cases stage <;> decide
  obtain ⟨s,hs⟩ := cur.advanceLocalWithPosition (pc' := pc+1) (G := fun _ => (tmp,b32 value)::F)
    (by
    intro lane hl
    have h := cur.checkpoint lane hl
    let u := next (setReg (cur.state lane) tmp (b32 value))
    have hr : run kernel [] l (warpLane l g lane) 1 (cur.state lane) = some u := by
      apply run_local hCode.1 rfl h
      cases stage <;> simp only [tmp,value,secondBroadcast,u] <;> rfl
    have hTau := localRun hLo (Nat.le_of_lt hHi) h.1 rfl hr
    refine ⟨u,run_rtg hTau,h.set ?_⟩
    intro pair hm he
    have hh := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hh
    exact hTmp hh)
  obtain ⟨out,hOut⟩ := s.consumeShuffleWithEvents (dst := dst) hp hMax hg .idx
    (fun _ => b32 value) (fun _ => 0) (fun _ => 31) (by
      intro _ _ pair hm
      rcases List.mem_cons.mp hm with he | hm
      · rw [he]
        exact hNe
      · intro he
        have hh := List.mem_map_of_mem (f := Prod.fst) hm
        rw [he] at hh
        exact hDst hh) (by
      intro lane hl
      have ht := s.checkpoint lane hl
      have h : (s.state lane).regs tmp = some (b32 value) := ht.2.2.2.2.1
      rw [out_eq_core (by rw [ht.1]; omega) (by rwa [ht.1]),
        out_event ht.2.2.2.1 (by rw [ht.1]; exact hCode.2) rfl rfl]
      change Out.ev (shflTmpl l (warpLane l g lane) (s.state lane) .idx dst none
        (.reg tmp) (.imm 0) (.imm 31) (.imm (-1))) = _
      have hBlock : l.block%32 = 0 := by rw [hp.block]
      simp [shflTmpl,readValue,readReg,h,hBlock,Value.bytes,b32,readBits,pure,Except.pure]
      rfl)
  refine ⟨out,?_⟩
  have h := samePollsOfShuffle hOut
  intro lane hl other
  rw [h lane hl other,hs]

private theorem steadyFinalSecondPvElectWithPolls (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g visit shuffles votes : Nat}
    (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2598 (fun _ => steadyTerminalPvFrame l visit)
      shuffles votes ends) :
    ∃ leader : Fin 32, ∃ out : SchedulerWarpReached l X g 2603
      (fun lane => pvElectedFrame l g 3 (2*visit+1) (visit%2) (decide (0<visit))
        (steadyTerminalPvFrame l visit) lane leader)
      (shuffles+2) votes ends,
      SamePolls l X g cur.pos out.pos := by
  obtain ⟨a,ha⟩ := secondBroadcastProgressWithPolls hp hMax hg false cur (by
    simp [secondBroadcast,steadyTerminalPvFrame]) (by simp [secondBroadcast,steadyTerminalPvFrame])
  obtain ⟨b,hb⟩ := secondBroadcastProgressWithPolls hp hMax hg true a (by
    simp [secondBroadcast,steadyTerminalPvFrame]) (by simp [secondBroadcast,steadyTerminalPvFrame])
  let F := pvEntryFacts l 3 (2*visit+1) (visit%2) (decide (0<visit)) ++
    steadyTerminalPvFrame l visit
  obtain ⟨c,hc⟩ := b.advanceLocalWithPosition (pc' := 2602) (G := fun _ => F) (by
    intro lane hl
    have ht := b.checkpoint lane hl
    have h := ht.2.2.2.2
    refine ⟨b.state lane,.refl,ht.mono ((holds_append ..).mpr ⟨?_,h.2.2.2.2⟩)⟩
    have hAcc : (if decide (0<visit) = true then 1 else 0) =
        (if 0<visit then 1 else 0) := by simp
    change Holds (b.state lane).regs
      [(2617,b32 384),(2616,b32 192),(2612,b32 (valueDescriptorLow l (2*visit+1))),
        (7206,b32 (if decide (0<visit) = true then 1 else 0)),
        (2618,b32 (l.sharedBase+120)),(7205,b32 (visit%2))]
    rw [hAcc]
    exact ⟨holds_lookup h rfl,holds_lookup h rfl,holds_lookup h rfl,holds_lookup h rfl,
      holds_lookup h rfl,holds_lookup h rfl,trivial⟩)
  have hPred : ∀ pair ∈ F, pair.1 ≠ 9738 := by
    intro pair hm he
    have hReg := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hReg
    have hCheck : 9738 ∉ F.map Prod.fst := by
      change 9738 ∉ [2617,2616,2612,7206,2618,7205,2612,2615,2618,7205,7206,1194,2535,6495]
      decide
    exact hCheck hReg
  obtain ⟨leader,w,hw⟩ := c.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (c.state lane) 16)
    (fun lane leader => (9738,.pred (laneOf l (warpLane l g lane) == leader)) :: F)
    (fun lane hl _ hj _ _ _ he =>
      noEarlierMmaElection 16 Flow.code_2602
        (by set_option maxRecDepth 100000 in kernel_rfl) (by kernel_rfl)
        (c.checkpoint lane hl) (c.recorded lane hl) (c.localSteps lane hl) hj he)
    (fun lane hl => electTemplate 16 (c.checkpoint lane hl))
    (fun lane hl leader => electStateFrame 16 (c.checkpoint lane hl) leader hPred
      (by simp [electSite]))
  refine ⟨leader,w,?_⟩
  have hcw := samePollsOfElect hw
  intro lane hl other
  rw [hcw lane hl other,hc,hb lane hl other,ha lane hl other]

private theorem pollsAfterSuccess {X : Execution} {thread pos : Nat} {loc : Loc}
    {pc phase : Nat} (hPos : 0 < pos)
    (he : X.get (thread,pos-1) = some ⟨pc,.wait loc phase true true .cta⟩) :
    okPolls loc ((X.tr thread).take pos) = okPolls loc ((X.tr thread).take (pos-1)) + 1 := by
  have h := countP_take_succ (p := okPoll loc) he (by simp [sourceWaitSuccess])
  rw [Nat.sub_add_cancel hPos] at h
  exact h

/-- From the final steady body at the exact poll counts of its last visit, the delivered
final V cohort and the four final probability cohorts take the warp through the terminal PV
packets to both output commits. The terminal V release retires use `2*visit+1`, and both
query buffers are returned on the way. -/
theorem steadyTerminalOfTailCohorts (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : Protocol.Scores.CorrectionJointGuards l X) {g visit shuffles votes : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2534 (fun _ => steadyFrame l visit 1) shuffles votes ends)
    (hValuePolls : ∀ lane < 32, okPolls ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩
      ((X.tr (warpLane l g lane)).take (cur.pos lane)) = (2*visit+1)/3)
    (hProbPolls : ∀ lane < 32, ∀ stage packet : Fin 2,
      okPolls (Thread.Scores.probabilityObject l (g/l.block) stage packet)
        ((X.tr (warpLane l g lane)).take (cur.pos lane)) = visit)
    (hValue : Protocol.LoaderReady.DeliveredCohort l X g (readyStage (2*visit+1)) ((2*visit+1)/3))
    (hProb : ∀ stage packet : Fin 2,
      Protocol.Scores.ProbabilityCohort l X (g/l.block) stage packet visit) :
    ∃ lastEnds, Nonempty (SchedulerWarpReached l X g 2647
      (fun _ => steadyTerminalPvFrame l visit) (shuffles+3+2) votes lastEnds) ∧
      TerminalOutputIssues l X g ∧ RetiredCacheUse l X g (2*visit+1) .tailValue ∧
      ∀ stage : Fin 2, ∃ issuer index, SameWarp l g issuer ∧
        X.Commit (issuer,index) (commitSpec l issuer (l.sharedBase+16+8*stage.val)) := by
  have hs := (readyStage (2*visit+1)).isLt
  have hCtaOf (lane : Nat) (hl : lane < 32) : (warpLane l g lane)/l.block = g/l.block :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.2.symm
  have hRoleOf (lane : Nat) (hl : lane < 32) : warpIndex l (warpLane l g lane) = 12 :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.2.symm.trans hw
  have hThreadOf (lane : Nat) (hl : lane < 32) : warpLane l g lane < l.threads :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.1
  -- Query returns and the final V acquire.
  obtain ⟨v,hV,hQuery⟩ := steadyTailValueWaitWithPolls hp hMax hg cur
  obtain ⟨m0,hM0⟩ := mmaWarpCachePollOfDelivered hp hMax hg hw 9 v
    (fun _ _ => by simp [steadyTailValueFrame,steadyFrame,steadyPorts,waitSite])
    (fun lane hl => by rw [hV lane hl]; exact hValuePolls lane hl) hValue
  have hM0Polls (lane : Nat) (hl : lane < 32) (other : Loc) :
      okPolls other ((X.tr (warpLane l g lane)).take (m0.pos lane)) =
        okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) +
          if other = ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩ then 1 else 0 := by
    rw [(hM0 lane hl).2.2.1 other,hV lane hl other]
  -- The final stage-zero main credit.
  obtain ⟨m1,hM1⟩ := mmaWarpProbabilityPollOfCohort hp hMax hGuard hg hw 10 0 0 m0
    (fun _ _ => by simp [steadyTailValueFrame,steadyFrame,steadyPorts,waitSite])
    (fun lane hl => by
      rw [hM0Polls lane hl,hProbPolls lane hl 0 0]
      simp only [Thread.Scores.probabilityObject,readyAddr,Loc.mk.injEq,true_and]
      split_ifs <;> omega)
    (hProb 0 0)
  obtain ⟨base,hBase⟩ := m1.advanceLocalWithPosition (pc' := 2551)
    (G := fun _ => (6495,b32 (l.sharedBase+144))::steadyTailValueFrame l visit) (by
      intro lane hl
      have ht := m1.checkpoint lane hl
      exact ⟨_,.refl,ht.mono
        ⟨finalOutputBaseOfMainReturned hp hMax hg hw m1 (fun lane hl => (hM1 lane hl).2.1)
          lane hl,ht.2.2.2.2⟩⟩)
  -- The first terminal PV packet under the final stage-zero tail credit.
  obtain ⟨leader,first,hFirst⟩ := steadyFinalFirstPvElectWithPolls hp hMax hg base
  have hFirstPolls (lane : Nat) (hl : lane < 32) (other : Loc) :
      okPolls other ((X.tr (warpLane l g lane)).take (first.pos lane)) =
        okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) +
          (if other = ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩ then 1 else 0) +
          (if other = ⟨.shared,g/l.block,l.sharedBase+(96+8*(0 : Fin 2).val+16*(0 : Fin 2).val)⟩
            then 1 else 0) := by
    rw [hFirst lane hl other,hBase,(hM1 lane hl).2.2.1 other,hM0Polls lane hl other]
  have hPhase : visit%2 < 2 := Nat.mod_lt _ (by decide)
  have hSetup (w : Fin 2) :
      ((kernel.code.drop ((electSite (pvElection (if w = 0 then 2 else 3))).pc+1)).take 7).all
        (fun ins => ((steadyTerminalPvFrame l visit).map Prod.fst).all
          (fun r => !(writesRegs ins.op).contains r)) = true := by
    rw [steadyTerminalRegisters]
    exact terminalPvSetup l w
  have hTail0 : ∀ lane < 32, PvTailReadyWithOrdinal l X (warpLane l g lane) 2 (visit%2)
      (steadyTerminalPvFrame l visit) (first.pos lane) := by
    intro lane hl
    right
    have hCta := hCtaOf lane hl
    change okPolls (Thread.Scores.probabilityObject l ((warpLane l g lane)/l.block) 0 1)
        (X.tr (warpLane l g lane)) =
      okPolls (Thread.Scores.probabilityObject l ((warpLane l g lane)/l.block) 0 1)
        ((X.tr (warpLane l g lane)).take (first.pos lane)) → _
    rw [hCta,hFirstPolls lane hl,hProbPolls lane hl 0 1]
    have hZero : (if Thread.Scores.probabilityObject l (g/l.block) 0 1 =
        ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩ then 1 else 0) +
        (if Thread.Scores.probabilityObject l (g/l.block) 0 1 =
          ⟨.shared,g/l.block,l.sharedBase+(96+8*(0 : Fin 2).val+16*(0 : Fin 2).val)⟩
          then 1 else 0) = 0 := by
      simp only [Thread.Scores.probabilityObject,readyAddr,Loc.mk.injEq,true_and]
      split_ifs <;> omega
    rw [Nat.add_assoc,hZero,Nat.add_zero]
    intro hTotal
    have hReady := Protocol.Scores.probabilityReadyOfUnconsumedCohort hp hMax.1 hGuard
      (g := warpLane l g lane) (gen := visit) (hThreadOf lane hl) (hRoleOf lane hl) 0 1
      (by rw [hCta]; exact hProb 0 1) (by rwa [hCta])
    rw [hCta] at hReady
    exact hReady
  obtain ⟨_,q,hIssue2,hQ⟩ := pvWarpPacketWithPollCounts hp hMax hg 2 (2*visit+1) (visit%2)
    (decide (0<visit)) hPhase leader (steadyTerminalExtra l visit 0) (hSetup 0) first hTail0
  have hQPolls (lane : Nat) (hl : lane < 32) (other : Loc) :
      okPolls other ((X.tr (warpLane l g lane)).take (q.pos lane)) =
        okPolls other ((X.tr (warpLane l g lane)).take (first.pos lane)) +
          if other = Thread.Scores.probabilityObject l (g/l.block) 0 1 then 1 else 0 := by
    rw [(hQ lane hl).2.2 other,hCtaOf lane hl]
    have hLoc : (⟨.shared,g/l.block,pvTailAddress l 2⟩ : Loc) =
        Thread.Scores.probabilityObject l (g/l.block) 0 1 := rfl
    rw [hLoc]
    by_cases h : other = Thread.Scores.probabilityObject l (g/l.block) 0 1 <;> simp [h]
  -- The final stage-one main credit.
  obtain ⟨r,hR⟩ := mmaWarpProbabilityPollOfCohort hp hMax hGuard hg hw 12 1 0 q
    (fun _ _ => by simp [steadyTerminalPvFrame,waitSite])
    (fun lane hl => by
      rw [hQPolls lane hl,hFirstPolls lane hl,hProbPolls lane hl 1 0]
      simp only [Thread.Scores.probabilityObject,readyAddr,Loc.mk.injEq,true_and]
      split_ifs <;> omega)
    (hProb 1 0)
  -- The second terminal PV packet under the final stage-one tail credit.
  obtain ⟨leader2,w,hW⟩ := steadyFinalSecondPvElectWithPolls hp hMax hg r
  have hTail1 : ∀ lane < 32, PvTailReadyWithOrdinal l X (warpLane l g lane) 3 (visit%2)
      (steadyTerminalPvFrame l visit) (w.pos lane) := by
    intro lane hl
    right
    have hCta := hCtaOf lane hl
    change okPolls (Thread.Scores.probabilityObject l ((warpLane l g lane)/l.block) 1 1)
        (X.tr (warpLane l g lane)) =
      okPolls (Thread.Scores.probabilityObject l ((warpLane l g lane)/l.block) 1 1)
        ((X.tr (warpLane l g lane)).take (w.pos lane)) → _
    rw [hCta,hW lane hl,(hR lane hl).2.2.1,hQPolls lane hl,hFirstPolls lane hl,
      hProbPolls lane hl 1 1]
    have hCount : visit +
        (if Thread.Scores.probabilityObject l (g/l.block) 1 1 =
          ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩ then 1 else 0) +
        (if Thread.Scores.probabilityObject l (g/l.block) 1 1 =
          ⟨.shared,g/l.block,l.sharedBase+(96+8*(0 : Fin 2).val+16*(0 : Fin 2).val)⟩
          then 1 else 0) +
        (if Thread.Scores.probabilityObject l (g/l.block) 1 1 =
          Thread.Scores.probabilityObject l (g/l.block) 0 1 then 1 else 0) +
        (if Thread.Scores.probabilityObject l (g/l.block) 1 1 =
          ⟨.shared,g/l.block,l.sharedBase+(96+8*(1 : Fin 2).val+16*(0 : Fin 2).val)⟩
          then 1 else 0) = visit := by
      simp only [Thread.Scores.probabilityObject,readyAddr,Loc.mk.injEq,true_and]
      split_ifs <;> omega
    rw [hCount]
    intro hTotal
    have hReady := Protocol.Scores.probabilityReadyOfUnconsumedCohort hp hMax.1 hGuard
      (g := warpLane l g lane) (gen := visit) (hThreadOf lane hl) (hRoleOf lane hl) 1 1
      (by rw [hCta]; exact hProb 1 1) (by rwa [hCta])
    rw [hCta] at hReady
    exact hReady
  obtain ⟨lastEnds,z,hIssue3,_⟩ := pvWarpPacketWithPollCounts hp hMax hg 3 (2*visit+1)
    (visit%2) (decide (0<visit)) hPhase leader2 (steadyTerminalExtra l visit 1) (hSetup 1) w hTail1
  -- The terminal V release, retiring use `2*visit+1`.
  obtain ⟨_,i,j,hij,h0⟩ := steadyTerminalCommitStep hp hMax hg 0 z
  have hIssue : Thread.Mma.ReleaseIssue X i j .tailValue
      (commitSpec l i (l.sharedBase+8*(readyStage (2*visit+1)).val+56)) := h0
  have hTarget : TcCommit.target
      (commitSpec l i (l.sharedBase+8*(readyStage (2*visit+1)).val+56)) 0 =
      some (Thread.Mma.Observation.emptyObject l i (readyStage (2*visit+1))) := by
    simp [TcCommit.target,commitSpec,Thread.Mma.Observation.emptyObject,
      Loader.emptySlot_address]
  obtain ⟨a⟩ := hIssue.matchReady hp hMax.1 hTarget
  have hSlot : a.slot = readyStage (2*visit+1) := by
    have h := congrArg Loc.addr a.target_eq
    simp only [Thread.Mma.Observation.emptyObject,Loader.emptySlot_address] at h
    exact Fin.ext (by omega)
  let li := laneOf l i
  have hl : li < 32 := Nat.mod_lt _ (by decide)
  have hThread : warpLane l g li = i := Step.warpLane_of_sameWarp hij
  have hBlock : i/l.block = g/l.block := hij.1.2.2.symm
  have hWait := (hM0 li hl).2.1
  rw [hThread] at hWait
  have hReadyAt : X.get (i,a.wait) = some ⟨2545,.wait
      (Thread.Mma.Observation.readyObject l i a.slot) a.parity true true .cta⟩ := a.readyForm
  have hSame := Thread.tailValueAcquireUnique hp hMax.1 (hij.2.symm.trans hw) hReadyAt hWait
  have hAfter := pollsAfterSuccess (by have := (hM0 li hl).1; omega) hWait
  have hCount := hM0Polls li hl ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩
  simp only [↓reduceIte] at hCount
  rw [hThread,hAfter] at hCount
  refine ⟨_,(steadyTerminalOutputCursor hp hMax hg z).1,
    (steadyTerminalOutputCursor hp hMax hg z).2,⟨i,j,hij,hIssue,a,hSlot,?_⟩,hQuery⟩
  rw [hSlot,Thread.Mma.atPrefix,Thread.Mma.kvAcquireCount,Loader.readySlot_address,hBlock,
    Nat.add_assoc,hSame]
  have hv := hValuePolls li hl
  rw [hThread] at hv
  change okPolls ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩ _ = _
  omega

/-- Published recurring cohorts, the delivered final V cohort and the four final probability
cohorts take the warp from the actual opening key return through every recurring visit, the
terminal visit and relinquish. The terminal V release retires use `2*(trips-1)+1`, and both
query buffers are returned. -/
theorem steadyTerminalAndRelinquishOfTailCohorts (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
    (hGuard : Protocol.Scores.CorrectionJointGuards l X) {g trips shuffles votes : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) {ends : Nat → Option TState} (hTrips : 2 ≤ trips)
    (hBound : trips < 2^31) (cur : OpeningKeyReturnedWithTrip l X g trips shuffles votes ends)
    (hCohorts : ∀ visit < trips-1, SteadyVisitCohorts l X g visit)
    (hValue : Protocol.LoaderReady.DeliveredCohort l X g
      (readyStage (2*(trips-1)+1)) ((2*(trips-1)+1)/3))
    (hProb : ∀ stage packet : Fin 2,
      Protocol.Scores.ProbabilityCohort l X (g/l.block) stage packet (trips-1)) :
    TerminalOutputIssues l X g ∧ MmaRelinquishPrefix l X g ∧
      (∀ visit < trips-1, SteadyIterationIssues l X g visit) ∧
      RetiredCacheUse l X g (2*(trips-1)+1) .tailValue ∧
      ∀ stage : Fin 2, ∃ issuer index, SameWarp l g issuer ∧
        X.Commit (issuer,index) (commitSpec l issuer (l.sharedBase+16+8*stage.val)) := by
  obtain ⟨_,_,fin,hLedger,hIssues⟩ :=
    steadyIterationsFromOpeningCohorts hp hMax hGuard hg hw hTrips hBound cur hCohorts
  obtain ⟨tail,hPos⟩ := fin.advanceLocalWithPosition (pc' := 2534)
    (G := fun _ => steadyFrame l (trips-1) 1) (by
      intro lane hl
      have ht := fin.checkpoint lane hl
      exact ⟨_,.refl,ht.mono ((holds_append ..).mp ht.2.2.2.2).1⟩)
  obtain ⟨_,⟨last⟩,hOutput,hRetired,hQuery⟩ := steadyTerminalOfTailCohorts hp hMax hGuard hg hw
    tail (fun lane hl => by
      rw [hPos]
      have h := hLedger.cache lane hl (readyStage (2*(trips-1)+1))
      have hCount : (2*(trips-1)+1+(2-(readyStage (2*(trips-1)+1)).val))/3 =
          (2*(trips-1)+1)/3 := by
        change (2*(trips-1)+1+(2-(2*(trips-1)+1)%3))/3 = _
        omega
      rw [hCount] at h
      exact h)
    (fun lane hl stage packet => by rw [hPos]; exact hLedger.probability lane hl stage packet)
    hValue hProb
  exact ⟨hOutput,relinquishAfterSteadyTerminalOutput hp hMax hCuQ hg hw last,hIssues,hRetired,
    hQuery⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
