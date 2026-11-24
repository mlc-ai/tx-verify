-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.EpilogueSchedulerProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.EpilogueFirstPassTrace
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
import Kernels.TmlFa4Fwd.Flow.Code.Part120
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part143
import Kernels.TmlFa4Fwd.Proof.EpilogueSearchWarp
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationTerminalExit
import Lemmas.Step.CtaBarNamed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

private def initialFrame (p : Params) (l : Launch) (g lane : Nat) : List (Nat × Value) :=
  [(7228,b32 p.batch),(7217,b32 (firstSchedulerWord p lane))] ++
    schedulerStartupFrame p l (warpLane l g lane)

private theorem firstWarpCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13) (hCuQ : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 2777 (initialFrame p l g) 3 0 ends) := by
  classical
  let thread := warpLane l g
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hC (lane : Nat) (hl : lane < 32) : ∃ j t u o,
      0 < j ∧ j ≤ (X.tr (thread lane)).length ∧ Softmax.beforeFirstScan X (thread lane) j ∧
      (j = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      At u 2777 (initialFrame p l g lane) ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take j) (some t) ∧
      Run kernel Assumptions.all l (thread lane) t ((X.tr (thread lane)).drop j) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) t u := by
    obtain ⟨hSame,hLane⟩ := Step.sameWarp_lane hBlock hg hl
    have hWarp := hSame.2.symm.trans hw
    obtain ⟨j,t,u,o,hPos,hBound,hCount,hReady,hAt,hPrefix,hTail,hLocal⟩ :=
      warp13ShuffleCursorOfMaximal hp hMax hSame.1.2.1 hWarp hCuQ
    have hLane' : laneOf l (warpLane l g lane) = lane := hLane
    have hAt' : At u 2777 (initialFrame p l g lane) := by
      change At u 2777 ([(7228,b32 p.batch),(7217,b32 (firstSchedulerWord p
        (laneOf l (warpLane l g lane))))] ++ schedulerStartupFrame p l (warpLane l g lane)) at hAt
      rw [hLane'] at hAt
      exact hAt
    exact ⟨j,t,u,o,hPos,hBound,hCount,hReady,hAt',hPrefix,hTail,hLocal⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! j t u o hPos hBound hCount hReady hAt hPrefix hTail hLocal using hC
  exact ⟨o,⟨⟨⟨j,t,u,⟨fun lane hl => (hCount lane hl).1,fun lane hl => (hCount lane hl).2⟩,
    hTail,hLocal,hAt⟩,hPos,hBound,hReady,hPrefix⟩⟩⟩

private def startup (p : Params) (l : Launch) (g lane : Nat) : List (Nat × Value) :=
  schedulerStartupFrame p l (warpLane l g lane)

private theorem startupRegisters {p : Params} {l : Launch} {g lane : Nat} {pair : Nat × Value}
    (hPair : pair ∈ startup p l g lane) : pair.1 ∈ firstPassRegs := by
  simp only [startup,schedulerStartupFrame,List.mem_cons,List.not_mem_nil,or_false] at hPair
  rcases hPair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [firstPassRegs,schedulerFrameRegs]

private def scanFrame (p : Params) (l : Launch) (g round lane : Nat) : List (Nat × Value) :=
  (firstPassScanReg round,b32 (prefixWindow (groupLaneTiles p 0) (2 ^ round) lane)) ::
    firstPassFacts p lane (startup p l g lane)

private theorem firstPassModel {l : Launch} {g : Nat} {s : TState}
    (hLo : 2778 ≤ s.pc) (hHi : s.pc < 2820) :
    out kernel Assumptions.all l g s = out kernel [] l g s :=
  epilogue_out_all_eq_nil (.inl ⟨by omega,by omega⟩)

private theorem firstOffsetEq (p : Params) (lane : Nat) :
    firstSchedulerWord p lane = firstPassOffset p lane := by
  by_cases h : lane ≤ p.batch
  · simp [firstSchedulerWord,firstPassOffset,h,Nat.not_lt_of_ge h]
  · simp [firstSchedulerWord,firstPassOffset,h,Nat.lt_of_not_ge h]

private theorem seedScan {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13) (hCuQ : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 2796 (scanFrame p l g 0) 4 0 ends) := by
  obtain ⟨ends,⟨cur⟩⟩ := firstWarpCursor hp hMax hg hw hCuQ
  obtain ⟨down⟩ := cur.consumeShuffle (dst := 2308) hp hMax hg .down
    (fun lane => b32 (firstSchedulerWord p lane)) (fun _ => 1) (fun _ => 31)
    (fun _ _ => by simp [initialFrame,schedulerStartupFrame])
    (fun lane hl => by
      have hAt := cur.checkpoint lane hl
      exact startupOut (.inr (.inr (by rw [hAt.1]; decide)))
        (schedulerFirstShuffle hp _ _ _ hAt.1 hAt.2.2.2.1 hAt.2.2.2.2.2.1))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  refine ⟨ends,down.advanceLocal (G := scanFrame p l g 0) (pc' := 2796) ?_⟩
  intro lane hl
  let thread := warpLane l g lane
  have hLane : laneOf l thread = lane := (Step.sameWarp_lane hBlock hg hl).2
  let F := startup p l g lane
  let extra := [(1201,b32 lane),(7228,b32 p.batch)] ++ F
  have hMember : ∀ pair ∈ extra, pair.1 ∈ firstPassRegs := by
    intro pair h
    simp only [extra,List.cons_append,List.nil_append,List.mem_cons] at h
    rcases h with rfl | rfl | h
    · simp [firstPassRegs,schedulerFrameRegs]
    · simp [firstPassRegs]
    · exact startupRegisters h
  have hAt := down.checkpoint lane hl
  have hFacts := hAt.2.2.2.2
  have hLaneReg : (down.state lane).regs 1201 = some (b32 lane) := by
    have h : (1201,b32 lane) ∈
      ((2308,b32 (firstSchedulerWord p (shflSource .down lane 1 31).1)) ::
        initialFrame p l g lane) := by
      have hLane' : laneOf l (warpLane l g lane) = lane := hLane
      simp [initialFrame,schedulerStartupFrame,hLane']
    exact holds_mem hFacts h
  have hSrc : (shflSource .down lane 1 31).1 = if lane < 31 then lane+1 else lane := by
    rw [shflSource_down_one lane]
    split <;> split <;> omega
  have hAt' : At (down.state lane) 2778
      ([(1201,b32 lane),(7228,b32 p.batch),(7217,b32 (firstPassOffset p lane)),
        (2308,b32 (firstPassOffset p (if lane < 31 then lane+1 else lane)))] ++ extra) := by
    rw [← firstOffsetEq,← firstOffsetEq,← hSrc]
    exact hAt.mono ⟨hLaneReg,hFacts.2.1,hFacts.2.2.1,hFacts.1,hLaneReg,hFacts.2.1,hFacts.2.2.2⟩
  obtain ⟨u, hu, hU⟩ := firstPassPrelude hp thread
    (fun hlo hhi => firstPassModel hlo (by omega)) hMember (by simpa only [hLane] using hAt')
  rw [hLane] at hU
  refine ⟨u,run_rtg hu,?_⟩
  simp only [scanFrame,firstPassScanReg,show 0 < 5 by decide,dite_eq_left,
    firstScanSrc,Nat.pow_zero,prefixWindow_one,firstPassFacts]
  exact hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2⟩


private theorem stableScanFrame {p : Params} {l : Launch} {g lane : Nat} {pair : Nat × Value}
    (hp : pair ∈ firstPassFacts p lane (startup p l g lane)) :
    pair.1 ∈ firstPassFrameRegs := by
  simp only [firstPassFacts,List.cons_append,List.nil_append,List.mem_cons] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | hp
  all_goals first
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (startupRegisters hp)))
    | simp [firstPassFrameRegs,firstPassRegs,schedulerFrameRegs]

private theorem scanRound {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (stage : Fin 5) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (firstScanPc stage)
      (scanFrame p l g stage.val) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (firstScanPc stage+4)
      (scanFrame p l g (stage.val+1)) (shuffles+1) votes ends) := by
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
  let F := fun lane => firstPassFacts p lane (startup p l g lane)
  have hReg : firstPassScanReg stage.val = firstScanSrc stage := by
    unfold firstPassScanReg
    rw [dite_eq_left stage.isLt]
  have hFresh : ∀ lane < 32, ∀ pair ∈ scanFrame p l g stage.val lane,
      pair.1 ≠ firstScanDst stage := by
    intro lane hl pair hm
    change pair ∈ (firstPassScanReg stage.val,b32 (part lane)) :: F lane at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · change firstPassScanReg stage.val ≠ firstScanDst stage
      rw [hReg]
      fin_cases stage <;> decide
    · have hStable := stableScanFrame hm
      intro hEq
      have hNone : firstScanDst stage ∉ firstPassFrameRegs := by fin_cases stage <;> decide
      exact hNone (hEq ▸ hStable)
  obtain ⟨read⟩ := cur.consumeShuffle (dst := firstScanDst stage) hp hMax hg .up
    (fun lane => b32 (part lane)) (fun _ => 2 ^ stage.val) (fun _ => 0) hFresh (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hWord := ht.2.2.2.2.1
      rw [hReg] at hWord
      rw [firstPassModel (by rw [ht.1]; simp [firstScanPc]; omega)
        (by rw [ht.1]; have := stage.isLt; simp [firstScanPc]; omega)]
      exact firstScanTemplate hp _ _ stage _ ht.1 ht.2.2.2.1 hWord)
  apply read.advanceLocal
  intro lane hl
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  let thread := warpLane l g lane
  have hLane : laneOf l thread = lane := (Step.sameWarp_lane hBlock hg hl).2
  let recv := (shflSource .up lane (2 ^ stage.val) 0).1
  have ht := read.checkpoint lane hl
  have hState : At (read.state lane) (firstScanPc stage+1)
      ([(1201,b32 lane),(firstScanSrc stage,b32 (part lane)),
          (firstScanDst stage,b32 (part recv))] ++ F lane) := by
    have hx := ht.2.2.2.2
    have hCarry : Holds (read.state lane).regs (F lane) := hx.2.2
    have hLaneVal : (read.state lane).regs 1201 = some (b32 lane) :=
      holds_mem hCarry (by simp [F,firstPassFacts] :
        (1201,b32 lane) ∈ F lane)
    have hPrev := hx.2.1
    rw [hReg] at hPrev
    exact ht.mono ⟨hLaneVal,hPrev,hx.1,hCarry⟩
  obtain ⟨u, hu, hU⟩ := firstPassFold hp thread stage (F := F lane)
    (fun hlo hhi => firstPassModel (by simp [firstScanPc] at hlo; omega)
      (by have := stage.isLt; simp [firstScanPc] at hhi; omega))
    (fun pair hm => stableScanFrame hm) (by simpa only [hLane,part,recv] using hState)
  refine ⟨u,run_rtg hu,?_⟩
  rw [hLane] at hU
  have hNext : firstPassScanReg (stage.val+1) = firstScanResult stage := by
    fin_cases stage <;> rfl
  have hWidth : 2 ^ (stage.val+1) = 2 * 2 ^ stage.val := by
    rw [Nat.pow_succ,Nat.mul_comm]
  simpa only [scanFrame,hNext,hWidth] using hU

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 13) (hCuQ : DrainCuQProtected p X)
include hp hMax hg hw hCuQ

private theorem throughFirstScan :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 2816 (scanFrame p l g 5) 9 0 ends) := by
  obtain ⟨ends,⟨s0⟩⟩ := seedScan hp hMax hg hw hCuQ
  obtain ⟨s1⟩ := scanRound hp hMax hg 0 s0
  obtain ⟨s2⟩ := scanRound hp hMax hg 1 s1
  obtain ⟨s3⟩ := scanRound hp hMax hg 2 s2
  obtain ⟨s4⟩ := scanRound hp hMax hg 3 s3
  exact ⟨ends,scanRound hp hMax hg 4 s4⟩



omit hp hMax hg hw hCuQ in
private def cutoffFrame (p : Params) (l : Launch) (g lane : Nat) : List (Nat × Value) :=
  firstGroupFacts p (g/l.block) lane (startup p l g lane)

private theorem throughFirstCutoff :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 2820 (cutoffFrame p l g) 10 0 ends) := by
  let part := fun lane => ∑ j ∈ Finset.range (lane+1), groupLaneTiles p 0 j
  let F := fun lane => firstPassFacts p lane (startup p l g lane)
  let H := fun lane => (7221,b32 (part lane)) :: F lane
  obtain ⟨ends,⟨cur⟩⟩ := throughFirstScan hp hMax hg hw hCuQ
  obtain ⟨ready⟩ := cur.advanceLocal (G := H) (pc' := 2816) (by
    intro lane hl
    refine ⟨cur.state lane,.refl,?_⟩
    have h := cur.checkpoint lane hl
    have he := prefixWindow_warp (groupLaneTiles p 0) hl
    change At (cur.state lane) 2816
      ((7221,b32 (prefixWindow (groupLaneTiles p 0) 32 lane)) :: F lane) at h
    rw [he] at h
    exact h)
  have hFresh (lane : Nat) (hl : lane < 32) (pair : Nat × Value) (hm : pair ∈ H lane) :
      pair.1 ≠ 7222 := by
    rcases List.mem_cons.mp hm with rfl | hm
    · change (7221 : Nat) ≠ 7222
      decide
    · intro eq
      have he : 7222 ∈ firstPassFrameRegs := eq ▸ stableScanFrame hm
      exact (of_decide_eq_true (by decide : decide (7222 ∉ firstPassFrameRegs) = true)) he
  obtain ⟨read⟩ := ready.consumeShuffle (dst := 7222) hp hMax hg .idx
    (fun lane => b32 (part lane)) (fun _ => 31) (fun _ => 31) hFresh (by
      intro lane hl
      have ht := ready.checkpoint lane hl
      rw [firstPassModel (by rw [ht.1]; decide) (by rw [ht.1]; decide)]
      exact firstGroupTotalTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1)
  refine ⟨ends,read.advanceLocal (G := cutoffFrame p l g) (pc' := 2820) ?_⟩
  intro lane hl
  let count := part 31
  let frame := (7222,b32 count) :: H lane
  have hFrame : ∀ pair ∈ frame, pair.1 ∈ firstPassLimitRegs := by
    intro pair hm
    simp only [frame,H,List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · simp [firstPassLimitRegs]
    · simp [firstPassLimitRegs]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (stableScanFrame hm))
  have ht := read.checkpoint lane hl
  have hs : At (read.state lane) 2817 frame := by
    simpa only [shflSource_idx lane (by decide : 31 < 32),frame,count] using ht
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1.1.2.2
  have hCta := (NamedBar.cta_lt hg).trans hp.grid.2.2
  have hCtaFact : (1072,b32 (g/l.block)) ∈ startup p l g lane := by
    simp [startup,schedulerStartupFrame,warpLane,hSame]
  have hAt : At (read.state lane) 2817 ([(7222,b32 count),(7138,b32 p.heads),
      (1072,b32 (g/l.block))] ++ frame) :=
    hs.mono ⟨hs.2.2.2.2.1,holds_mem hs.2.2.2.2 (by simp [frame,H,F,firstPassFacts]),
      holds_mem hs.2.2.2.2 (by simp [frame,H,F,firstPassFacts,hCtaFact]),hs.2.2.2.2⟩
  obtain ⟨u,hu,hU⟩ := firstPassLimit hp (warpLane l g lane) hCta
    (fun lo hi => firstPassModel (by omega) hi) hFrame hAt
  exact ⟨u,run_rtg hu,hU⟩



/-- An idle output warp exhausts all request groups and records its exit. -/
theorem idleWarp13ExitOfAllGroups (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  obtain ⟨ends,⟨cur⟩⟩ := throughFirstCutoff hp hMax hg hw hCuQ
  let old : FirstGroupCutoff p l Assumptions.all X g (g/l.block) (startup p l g) 10 0 ends :=
    ⟨cur.pos,cur.before,cur.state,cur.ordinals,cur.continuation,cur.localSteps,cur.checkpoint⟩
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCtaFact : ∀ lane < 32, (1072,b32 (g/l.block)) ∈ startup p l g lane := by
    intro lane hl
    have hSame := (Step.sameWarp_lane hBlock hg hl).1.1.2.2
    simp [startup,schedulerStartupFrame,warpLane,hSame]
  have hCTA := NamedBar.cta_lt hg
  have hSkip : tilePrefix p (min p.batch 31) * p.heads ≤ g/l.block := by
    exact (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left ..))).trans hIdle
  have hRegs : ∀ lane < 32, ∀ pair ∈ startup p l g lane, pair.1 ∈ schedulerFrameRegs := by
    intro lane hl pair hm
    simp only [startup,schedulerStartupFrame,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [schedulerFrameRegs]
  obtain ⟨seed,hPos,hState⟩ := old.enterSearchPreserving hSkip (hCTA.trans hp.grid.2.2)
    hRegs hCtaFact
  have hBase : ∀ lane < 32, (7506, b64 p.cuQBase) ∈ startup p l g lane := by
    intro lane hl
    simp [startup, schedulerStartupFrame]
  have hWarp : ∀ lane < 32, (1062, b32 13) ∈ startup p l g lane := by
    intro lane hl
    simp [startup, schedulerStartupFrame]
  obtain ⟨_, ⟨done⟩⟩ := (cur.reframe seed hPos hState).idleSearchExhausted hp hMax hg hCTA
    hIdle hRegs hBase hWarp hCuQ hp.shape.1
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨v, hLocal, hv, hFault, hWarp⟩ := done.toSchedulerWarpAt.exitWithoutTileLocal hp lane hl
  rw [hSelf] at hLocal
  have hModel {s : TState} (hs : s.pc ∈ [3099,3100,7742,7743,7744,9205]) :
      out kernel Assumptions.all l g s = out kernel [] l g s := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    apply epilogue_out_all_eq_nil
    unfold EpiloguePc
    omega
  obtain ⟨u,hu,_,hOut⟩ := finishSchedulerOfWarpWith l g v hModel hv hFault (.inr rfl) hWarp
  have hn : Next kernel Assumptions.all l g (done.before lane) u .exit :=
    ⟨hLocal.trans (run_rtg hu),hOut⟩
  refine ⟨done.pos lane,_,Thread.exitAtMaximalCursor (o := ends lane) hMax hg
    (done.positive lane hl)
    ?_ ?_ ?_ hn ?_,rfl⟩
  · simpa only [hSelf] using done.bounded lane hl
  · simpa only [hSelf] using done.recorded lane hl
  · simpa only [hSelf] using done.continuation lane hl
  · simpa only [hSelf] using done.released lane hl


/-- An idle output warp records its exit in the short batch case. -/
theorem idleWarp13Exit (_hBatch : p.batch ≤ 31) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block)
    :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit :=
  idleWarp13ExitOfAllGroups hp hMax hg hw hCuQ hIdle



/-- The scheduled output warp reaches the selected group's real ballot in any maximal trace. -/
theorem selectedOutputBallotOfMaximal (hActive : g / l.block < tilePrefix p p.batch * p.heads) :
    ∃ first < p.batch, tilePrefix p first * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (min p.batch (first + 31)) * p.heads ∧
      ∃ shuffles ends, Nonempty (SchedulerWarpReached l X g 2883
        (fun lane => groupChoiceFacts p (g / l.block) first lane
          (schedulerStartupFrame p l (warpLane l g lane)))
        shuffles 0 ends) := by
  obtain ⟨ends,⟨cur⟩⟩ := throughFirstCutoff hp hMax hg hw hCuQ
  let cta := g / l.block
  let F := startup p l g
  let old : FirstGroupCutoff p l Assumptions.all X g cta F 10 0 ends :=
    ⟨cur.pos,cur.before,cur.state,cur.ordinals,cur.continuation,cur.localSteps,cur.checkpoint⟩
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCtaFact : ∀ lane < 32, (1072,b32 cta) ∈ F lane := by
    intro lane hl
    have hSame := (Step.sameWarp_lane hBlock hg hl).1.1.2.2
    simp [F,cta,startup,schedulerStartupFrame,warpLane,hSame]
  have hFrame : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs :=
    fun lane _ => schedulerStartupFramed p l (warpLane l g lane)
  have hBase : ∀ lane < 32, (7506,b64 p.cuQBase) ∈ F lane := by
    intro lane _
    simp [F,startup,schedulerStartupFrame]
  have hCTA := NamedBar.cta_lt hg
  by_cases hFirst : cta < tilePrefix p (min p.batch 31) * p.heads
  · obtain ⟨selected,hPos,hBefore⟩ := old.enterSelectionPreserving hp hFirst hFrame hCtaFact
    refine ⟨0,hp.shape.1,?_,?_,10,ends,⟨cur.reframe selected hPos hBefore⟩⟩
    · simp [tilePrefix]
    · simpa using hFirst
  · have hPast := Nat.le_of_not_gt hFirst
    obtain ⟨seed,hPos,hBefore⟩ :=
      old.enterSearchPreserving hPast (hCTA.trans hp.grid.2.2) hFrame hCtaFact
    obtain ⟨first,shuffles,hSelected,hLo,hHi,⟨available⟩⟩ :=
      (cur.reframe seed hPos hBefore).selectedSearchGroupOfMaximal hp hMax hg hCTA hActive
        hFrame hBase hCuQ hp.shape.1 (by simpa using hPast)
    obtain ⟨selected,hPos,hBefore⟩ :=
      available.toSchedulerWarpAt.enterBatchSelectionPreserving hp hSelected hFrame
    exact ⟨first,hSelected,hLo,hHi,shuffles,ends,⟨available.reframe selected hPos hBefore⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
