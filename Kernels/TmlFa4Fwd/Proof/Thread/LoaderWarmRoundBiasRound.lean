-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasChain
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.MBarrier Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The readiness of warp 14's Bias-empty waits in warm round `round`. At either stage's
wait, a lane whose remaining trace consists of failed polls finds the object in the phase
that lets the poll pass. The checkpoint supplies the warp's positions, its scheduler
registers and its per-site election counts. -/
def WarmBiasEmptyReady (l : Launch) (X : Execution) (g batch round : Nat) : Prop :=
  ∀ (stage : Fin 2) {F : Nat → List (Nat × Value)} {shuffles votes : Nat}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmBiasEmptyWait stage).pc F shuffles votes ends),
    shuffles = primingSearchShuffleCount batch+96+64*round →
    (∀ lane < 32, Holds (cur.state lane).regs [(2535,b32 l.sharedBase),(1062,b32 14)]) →
    (∀ lane < 32, ∀ k, round ≤ warmBiasSiteCount X (warpLane l g lane) (cur.pos lane) k) →
    ∀ lane < 32,
      (∀ e ∈ (X.tr (warpLane l g lane)).drop (cur.pos lane),
        ∃ loc, e.kind = .wait loc (round%2) false true .cta) →
      let log := X.objects (biasEmptyObject l (g/l.block) stage)
      ∃ s, stateBefore log log.length = some s ∧ s.phase%2 ≠ round%2

/-- The Bias packets that warp 14 issues in warm round `round`, and the per-site election
counts that the next round's elections rely on. -/
structure WarmRoundBiasIssued (p : Params) (l : Launch) (X : Execution) (g batch round : Nat) :
    Prop where
  expectation : ∀ stage : Fin 2, ∃ issue, issue.1/l.block = g/l.block ∧
    X.get issue = some ⟨warmBiasSite (warmBiasExpectSite stage)+4,
      .arrive (biasReadyObject l (g/l.block) stage) 32768 1 true .cta⟩ ∧
    ((X.tr issue.1).take issue.2).countP Execution.isShfl =
      primingSearchShuffleCount batch+96+64*round
  boxes : ∀ stage half : Fin 2, ∃ issue, issue.1/l.block = g/l.block ∧
    X.get issue = some ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress
      (inputSiteSpec p l issue.1 (inputSite (warmBiasInputSite stage half))
        (warmBiasColumn stage half round (warmBiasBit p l g batch))
        (warmBiasStageRow (warmBiasRow p l g batch) stage) (warmBiasHead p l g batch)
        (warmBiasStageBarrier l stage))⟩ ∧
    ((X.tr issue.1).take issue.2).countP Execution.isShfl =
      primingSearchShuffleCount batch+96+64*round
  counted : ∀ lane < 32, ∀ k pos,
    primingSearchShuffleCount batch+96+64*round <
      ((X.tr (warpLane l g lane)).take pos).countP Execution.isShfl →
    round+1 ≤ warmBiasSiteCount X (warpLane l g lane) pos k

set_option maxRecDepth 4096 in
private theorem stageFrameRegs {p : Params} {l : Launch} {g batch round lane : Nat}
    (hw : warpIndex l g = 14) (stage : Fin 2) {R : Nat → Option Value}
    (h : Holds R (warmRoundBiasStageFrame p l g batch round stage lane)) :
    Holds R [(2535,b32 l.sharedBase),(1062,b32 14)] := by
  have hC : Holds R (warmRoundValueCarry p l g batch round lane) := by
    fin_cases stage
    · exact h.2.2.2
    · exact h.2.2.2.2
  refine ⟨holds_mem hC ?_,holds_mem hC ?_,trivial⟩
  · simp [warmRoundValueCarry,warmRoundKeyCarry,warmRoundPagesFrame,warmRoundFrame,
      openingWarmFrame,warmStartFrame]
  · simp [warmRoundValueCarry,warmRoundKeyCarry,warmRoundPagesFrame,warmRoundFrame,
      openingWarmFrame,warmStartFrame,hw]

set_option maxRecDepth 4096 in
private theorem stageFrameWait {p : Params} {l : Launch} {g batch round : Nat}
    (hw : warpIndex l g = 14) (stage : Fin 2) (lane : Nat) :
    (∀ pair ∈ warmRoundBiasStageFrame p l g batch round stage lane,
      pair.1 ≠ (warmBiasEmptyWait stage).result) ∧
    ((warmBiasEmptyWait stage).base,b32 (l.sharedBase+(336+8*stage.val))) ∈
      warmRoundBiasStageFrame p l g batch round stage lane ∧
    ((warmBiasEmptyWait stage).phase,b32 (round%2)) ∈
      warmRoundBiasStageFrame p l g batch round stage lane := by
  refine ⟨fun pair hm => ?_,?_,?_⟩
  · have h : ((warmRoundBiasStageFrame p l g batch round stage lane).map Prod.fst).all
        (fun r => decide (r ≠ 9613 ∧ r ≠ 9614)) = true := by
      fin_cases stage <;> (set_option maxRecDepth 100000 in rfl)
    have := of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
    fin_cases stage <;> simp [warmBiasEmptyWait] <;> omega
  · fin_cases stage <;> simp [warmBiasEmptyWait,warmRoundBiasStageFrame,warmRoundBiasFrame]
  · have hWord := warmBiasPhaseWord round
    fin_cases stage <;>
      simp [warmBiasEmptyWait,warmRoundBiasStageFrame,warmRoundBiasFrame,warmRoundValueCarry,
        warmRoundKeyCarry,warmRoundPagesFrame,warmRoundFrame,hw,← hWord]

set_option maxRecDepth 4096 in
/-- From the K publication of warm round `round`, warp 14 issues both Bias stages of the
round, passes the V poll and publishes the round's V packet. The release hypotheses are the
MMA's return of the V slot and the softmax readiness of both Bias-empty objects; the
count hypothesis is the result of the previous round's elections. -/
theorem WarmRoundKeyPublished.biasRoundOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRound : round < warmRounds p l g batch)
    (hReady : WarmBiasEmptyReady l X g batch round)
    (hReleased : (cacheUseOfRound round+1)/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round+1)))
    (c : WarmRoundKeyPublished p l X g batch round)
    (hLower : ∀ lane < 32, ∀ k,
      round ≤ warmBiasSiteCount X (warpLane l g lane) (c.reached.pos lane) k) :
    Nonempty (WarmRoundValuePublished p l X g batch round) ∧
      WarmRoundBiasIssued p l X g batch round := by
  unfold WarmBiasEmptyReady at hReady
  have hRank := c.rank
  have hFive : 5 ≤ c.shuffles := by rw [hRank]; omega
  let S := warmRoundBiasStageFrame p l g batch round
  -- Gate and Bias map.
  obtain ⟨gate,hGate⟩ := c.biasGate hp hw
  obtain ⟨gate0,hGate0⟩ := gate.advanceLocalWithPosition (pc' := 1146) (G := S 0)
    (fun lane hl => ⟨gate.state lane,.refl,(gate.checkpoint lane hl).mono
      ⟨warmBiasMapAt hp hMax.1 hg (by omega) (by decide) hFive gate lane hl,
        (gate.checkpoint lane hl).2.2.2.2⟩⟩)
  have hPos0 : gate0.pos = c.reached.pos := hGate0.trans hGate
  -- Stage zero.
  obtain ⟨wait0,hWait0⟩ := warmBiasEmptyAcquireOfMaximal hp hMax hg 0 (round := round)
    (gate0 : SchedulerWarpReached l X g (warmBiasEmptyWait 0).pc (S 0) c.shuffles c.votes
      c.ends)
    (fun lane _ => (stageFrameWait hw 0 lane).1) (fun lane _ => (stageFrameWait hw 0 lane).2.1)
    (fun lane _ => (stageFrameWait hw 0 lane).2.2)
    (hReady 0 gate0 hRank (fun lane hl => stageFrameRegs hw 0 (gate0.checkpoint lane hl).2.2.2.2)
      (fun lane hl k => by rw [hPos0]; exact hLower lane hl k))
  have hW0 (lane : Nat) (hl : lane < 32) :
      c.reached.pos lane ≤ wait0.pos lane ∧
        QuietSpan X (warpLane l g lane) (c.reached.pos lane) (wait0.pos lane) := by
    have h := hWait0 lane hl
    rw [hPos0] at h
    exact ⟨h.1.le,h.2⟩
  have lower {pos : Nat → Nat} (hp' : ∀ lane < 32, c.reached.pos lane ≤ pos lane)
      (lane : Nat) (hl : lane < 32) (k : Fin 6) :
      round ≤ warmBiasSiteCount X (warpLane l g lane) (pos lane) k :=
    (hLower lane hl k).trans (warmBiasSiteCount_mono X k (hp' lane hl))
  obtain ⟨exp0,hExp0,iss0,hIss0Cta,hIss0,hIss0Rank⟩ := warmRoundBiasExpectOfMaximal hp hMax
    hFrame hg hw hb hLo hHi 0
    (wait0 : SchedulerWarpReached l X g (warmBiasSite (warmBiasExpectSite 0)) (S 0) c.shuffles
      c.votes c.ends) hRank (fun lane hl => lower (fun q hq => (hW0 q hq).1) lane hl _)
  have hE0 (lane : Nat) (hl : lane < 32) :
      c.reached.pos lane ≤ exp0.pos lane ∧
        QuietSpan X (warpLane l g lane) (c.reached.pos lane) (exp0.pos lane) := by
    have h := hExp0 lane hl
    exact ⟨(hW0 lane hl).1.trans h.1.le,(hW0 lane hl).2.trans h.2.1⟩
  obtain ⟨box00,hBox00,b00,hB00Cta,hB00,hB00Rank⟩ := warmRoundBiasBoxOfMaximal hp hMax hFrame
    hg hw hb hLo hHi hRound 0 0
    (exp0 : SchedulerWarpReached l X g (warmBiasSite (warmBiasBoxSite 0 0)) (S 0) c.shuffles
      c.votes c.ends) hRank (fun lane hl => lower (fun q hq => (hE0 q hq).1) lane hl _)
  have hX00 (lane : Nat) (hl : lane < 32) :
      c.reached.pos lane ≤ box00.pos lane ∧
        QuietSpan X (warpLane l g lane) (c.reached.pos lane) (box00.pos lane) := by
    have h := hBox00 lane hl
    exact ⟨(hE0 lane hl).1.trans h.1.le,(hE0 lane hl).2.trans h.2.1⟩
  obtain ⟨box01,hBox01,b01,hB01Cta,hB01,hB01Rank⟩ := warmRoundBiasBoxOfMaximal hp hMax hFrame
    hg hw hb hLo hHi hRound 0 1
    (box00 : SchedulerWarpReached l X g (warmBiasSite (warmBiasBoxSite 0 1)) (S 0) c.shuffles
      c.votes c.ends) hRank (fun lane hl => lower (fun q hq => (hX00 q hq).1) lane hl _)
  have hX01 (lane : Nat) (hl : lane < 32) :
      c.reached.pos lane ≤ box01.pos lane ∧
        QuietSpan X (warpLane l g lane) (c.reached.pos lane) (box01.pos lane) := by
    have h := hBox01 lane hl
    exact ⟨(hX00 lane hl).1.trans h.1.le,(hX00 lane hl).2.trans h.2.1⟩
  -- Stage one.
  obtain ⟨gate1,hGate1⟩ := box01.advanceLocalWithPosition (pc' := 1175) (G := S 1) (by
    intro lane hl
    have hs := box01.checkpoint lane hl
    have hSeg : Seg kernel [] l (warpLane l g lane) 1 1174 [(2535,b32 l.sharedBase)] 1175
        [(2052,b32 (l.sharedBase+344))] := by
      have hMem := hp.shared.2.1
      have hBase : l.sharedBase < 2^32 := by omega
      have hEmpty : l.sharedBase+344 < 2^32 := by omega
      intro s h
      seg_fp h using norm_bits [Nat.mod_eq_of_lt hBase,Nat.mod_eq_of_lt hEmpty]
    have hRoot : (box01.state lane).regs 2535 = some (b32 l.sharedBase) :=
      (stageFrameRegs hw 0 hs.2.2.2.2).1
    obtain ⟨v,hv,hV⟩ := roundStraightFrame (F := S 0 lane) (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hSeg
      (hs.mono ⟨hRoot,hs.2.2.2.2⟩)
    exact ⟨v,run_rtg hv,hV⟩)
  have hPos1 : gate1.pos = box01.pos := hGate1
  obtain ⟨wait1,hWait1⟩ := warmBiasEmptyAcquireOfMaximal hp hMax hg 1 (round := round)
    (gate1 : SchedulerWarpReached l X g (warmBiasEmptyWait 1).pc (S 1) c.shuffles c.votes
      c.ends)
    (fun lane _ => (stageFrameWait hw 1 lane).1) (fun lane _ => (stageFrameWait hw 1 lane).2.1)
    (fun lane _ => (stageFrameWait hw 1 lane).2.2)
    (hReady 1 gate1 hRank (fun lane hl => stageFrameRegs hw 1 (gate1.checkpoint lane hl).2.2.2.2)
      (fun lane hl k => by rw [hPos1]; exact lower (fun q hq => (hX01 q hq).1) lane hl k))
  have hW1 (lane : Nat) (hl : lane < 32) :
      c.reached.pos lane ≤ wait1.pos lane ∧
        QuietSpan X (warpLane l g lane) (c.reached.pos lane) (wait1.pos lane) := by
    have h := hWait1 lane hl
    rw [hPos1] at h
    exact ⟨(hX01 lane hl).1.trans h.1.le,(hX01 lane hl).2.trans h.2⟩
  obtain ⟨exp1,hExp1,iss1,hIss1Cta,hIss1,hIss1Rank⟩ := warmRoundBiasExpectOfMaximal hp hMax
    hFrame hg hw hb hLo hHi 1
    (wait1 : SchedulerWarpReached l X g (warmBiasSite (warmBiasExpectSite 1)) (S 1) c.shuffles
      c.votes c.ends) hRank (fun lane hl => lower (fun q hq => (hW1 q hq).1) lane hl _)
  have hE1 (lane : Nat) (hl : lane < 32) :
      c.reached.pos lane ≤ exp1.pos lane ∧
        QuietSpan X (warpLane l g lane) (c.reached.pos lane) (exp1.pos lane) := by
    have h := hExp1 lane hl
    exact ⟨(hW1 lane hl).1.trans h.1.le,(hW1 lane hl).2.trans h.2.1⟩
  obtain ⟨box10,hBox10,b10,hB10Cta,hB10,hB10Rank⟩ := warmRoundBiasBoxOfMaximal hp hMax hFrame
    hg hw hb hLo hHi hRound 1 0
    (exp1 : SchedulerWarpReached l X g (warmBiasSite (warmBiasBoxSite 1 0)) (S 1) c.shuffles
      c.votes c.ends) hRank (fun lane hl => lower (fun q hq => (hE1 q hq).1) lane hl _)
  have hX10 (lane : Nat) (hl : lane < 32) :
      c.reached.pos lane ≤ box10.pos lane ∧
        QuietSpan X (warpLane l g lane) (c.reached.pos lane) (box10.pos lane) := by
    have h := hBox10 lane hl
    exact ⟨(hE1 lane hl).1.trans h.1.le,(hE1 lane hl).2.trans h.2.1⟩
  obtain ⟨box11,hBox11,b11,hB11Cta,hB11,hB11Rank⟩ := warmRoundBiasBoxOfMaximal hp hMax hFrame
    hg hw hb hLo hHi hRound 1 1
    (box10 : SchedulerWarpReached l X g (warmBiasSite (warmBiasBoxSite 1 1)) (S 1) c.shuffles
      c.votes c.ends) hRank (fun lane hl => lower (fun q hq => (hX10 q hq).1) lane hl _)
  have hX11 (lane : Nat) (hl : lane < 32) :
      c.reached.pos lane ≤ box11.pos lane ∧
        QuietSpan X (warpLane l g lane) (c.reached.pos lane) (box11.pos lane) := by
    have h := hBox11 lane hl
    exact ⟨(hX10 lane hl).1.trans h.1.le,(hX10 lane hl).2.trans h.2.1⟩
  -- Phase flips, V gate and V packet.
  let bias' := loaderPhaseWord (warmBiasPhase (warpIndex l g) (round+1))
  obtain ⟨vgate,hVGate⟩ := box11.advanceLocalWithPosition (pc' := (recurringEmptyWait 1).pc)
    (G := fun lane => recurringBarrierFacts l 1 (kvUseStage (cacheUseOfRound round+1))
      (cacheEmptyParity (cacheUseOfRound round+1)) ++
        warmRoundVCarry p l g batch round bias' lane)
    (fun lane hl => warmRoundBiasFlipLocal hp hw (box11.checkpoint lane hl))
  have hFresh : ∀ lane < 32, (recurringEmptyWait 1).result ∉
      (warmRoundVCarry p l g batch round bias' lane).map Prod.fst :=
    fun _ _ => of_decide_eq_true rfl
  obtain ⟨done,hDone⟩ := RecurringCacheGate.acquireOfReleases hp hMax hFrame hg (by omega) hb
    hLo hHi 1 (vgate : RecurringCacheGate l X g 1 (cacheUseOfRound round+1)
      (warmRoundVCarry p l g batch round bias') c.shuffles c.votes c.ends) hFresh
    (by rw [hRank]; unfold cacheUseOfRound; omega) (by unfold cacheUseOfRound; omega) hReleased
  have hCells (lane : Nat) (hl : lane < 32) (slot : Fin 2) (isRow : Bool) :
      warmRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
    have hSpan := (hX11 lane hl).2
    rw [← congrFun hVGate lane] at hSpan
    have hAll := hSpan.trans (fun i h₁ h₂ => (hDone lane hl).2 i h₁ h₂)
    obtain ⟨index,hLe,hIdx,_⟩ := (hDone lane hl).1
    have hMid : box11.pos lane ≤ done.pos lane := by
      rw [← congrFun hVGate lane]
      omega
    exact PrimingCellValue.ofQuietSpan (c.metadata lane hl slot isRow)
      ((hX11 lane hl).1.trans hMid) hAll
  refine ⟨warmRoundValuePublishedOfMaximal hp hMax hg (by omega) hb hLo hHi rfl hRank done
    hCells,?_⟩
  -- The Bias facts of the round.
  have hEnd (lane : Nat) (hl : lane < 32) (k : Fin 6) :
      round+1 ≤ warmBiasSiteCount X (warpLane l g lane) (box11.pos lane) k := by
    have q1 := (hBox00 lane hl).1
    have q2 := (hBox01 lane hl).1
    have q3 := (hWait1 lane hl).1
    rw [hPos1] at q3
    have q4 := (hExp1 lane hl).1
    have q5 := (hBox10 lane hl).1
    have q6 := (hBox11 lane hl).1
    have mono {a b : Nat} (h : a ≤ b) :=
      warmBiasSiteCount_mono X (t := warpLane l g lane) k h
    have me0 := mono (show exp0.pos lane ≤ box11.pos lane by omega)
    have m00 := mono (show box00.pos lane ≤ box11.pos lane by omega)
    have m01 := mono (show box01.pos lane ≤ box11.pos lane by omega)
    have me1 := mono (show exp1.pos lane ≤ box11.pos lane by omega)
    have m10 := mono (show box10.pos lane ≤ box11.pos lane by omega)
    have c0 := (hExp0 lane hl).2.2
    have c1 := (hBox00 lane hl).2.2
    have c2 := (hBox01 lane hl).2.2
    have c3 := (hExp1 lane hl).2.2
    have c4 := (hBox10 lane hl).2.2
    have c5 := (hBox11 lane hl).2.2
    fin_cases k
    · exact c0.trans me0
    · exact c1.trans m00
    · exact c2.trans m01
    · exact c3.trans me1
    · exact c4.trans m10
    · exact c5
  have hEndRank (lane : Nat) (hl : lane < 32) :
      ((X.tr (warpLane l g lane)).take (box11.pos lane)).countP Execution.isShfl =
        primingSearchShuffleCount batch+96+64*round :=
    (box11.ordinals.shfl lane hl).trans hRank
  refine ⟨fun stage => ?_,fun stage half => ?_,fun lane hl k pos hPos => ?_⟩
  · fin_cases stage
    · exact ⟨iss0,hIss0Cta,hIss0,hIss0Rank.trans hRank⟩
    · exact ⟨iss1,hIss1Cta,hIss1,hIss1Rank.trans hRank⟩
  · fin_cases stage <;> fin_cases half
    · exact ⟨b00,hB00Cta,hB00,hB00Rank.trans hRank⟩
    · exact ⟨b01,hB01Cta,hB01,hB01Rank.trans hRank⟩
    · exact ⟨b10,hB10Cta,hB10,hB10Rank.trans hRank⟩
    · exact ⟨b11,hB11Cta,hB11,hB11Rank.trans hRank⟩
  · have hAfter : box11.pos lane ≤ pos := by
      by_contra! hLt
      have := countP_take_mono Execution.isShfl (X.tr (warpLane l g lane)) hLt.le
      have := hEndRank lane hl
      omega
    exact (hEnd lane hl k).trans (warmBiasSiteCount_mono X k hAfter)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
