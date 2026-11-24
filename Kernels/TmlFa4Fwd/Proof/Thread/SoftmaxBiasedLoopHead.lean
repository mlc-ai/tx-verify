-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedScoreProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorScoreCount
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreBiasProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreNumericsProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedAffineOrdinals
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePollCount
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank
import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScorePollRanks
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded
import Kernels.TmlFa4Fwd.Proof.Safety.TmemWordSizes
import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue Thread Correction

/-- The registers live at the head of the biased loop (pc 5032) in every visit. The score,
Bias and correction parities all equal the visit parity. -/
def biasedHeadFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) (visit block : Nat)
    (maximum : Option ℝ) (sum : ℝ) (floor counter : Nat) : List (Nat × Value) :=
  (1062,b32 warp.val)::(2535,b32 l.sharedBase)::(7253,b32 (visit%2))::(7249,b32 block)::
    (openingDenominatorRegisters p l g ++
      [(7251,scoreValue maximum),(7257,fl sum),(1361,b32 floor),(7258,b32 (visit%2)),
        (7250,b32 (visit%2)),(7248,b32 counter)])

/-- The register facts kept from the head to the score loads. -/
def biasedHeadKept (p : Params) (l : Launch) (g : Nat) (visit : Nat)
    (maximum : Option ℝ) (sum : ℝ) (floor counter : Nat) : List (Nat × Value) :=
  openingDenominatorRegisters p l g ++
    [(7251,scoreValue maximum),(7257,fl sum),(1361,b32 floor),(7258,b32 (visit%2)),
      (7250,b32 (visit%2)),(7248,b32 counter)]

/-- The loop geometry registers fixed for the whole repeated loop of a lane. -/
def loopGeometry (blocks split pastTile : Nat) : List (Nat × Value) :=
  [(1226,b32 blocks),(1229,b32 (blocks-1)),(1225,b32 (pastTile+256)),
    (1360,b32 (pastTile/128)),(1359,b32 split)]

/-- The four per-lane event counts that warp-collective and statistics steps need. -/
def SoftmaxCounts (X : Execution) (g i tc bars elects notices credits scores : Nat) : Prop :=
  ((X.tr g).take i).countP isTcColl = tc ∧ warpBars X g i = bars ∧ elections X g i = elects ∧
    ((X.tr g).take i).countP Scores.publishesStats = notices ∧
    ((X.tr g).take i).countP Scores.creditAcquired = credits ∧
    ((X.tr g).take i).countP scoreAcquired = scores

/-- A window of failed polls followed by one successful poll keeps all four counts. -/
theorem SoftmaxCounts.ofPolls {X : Execution}
    {g start index stop tc bars elects notices credits scores : Nat}
    {pc phase : Nat} {object : Loc} (hStart : start ≤ index) (hStop : stop = index+1)
    (hTrace : (X.tr g).drop start = List.replicate (index-start)
      ⟨pc,.wait object phase false true .cta⟩ ++
      ⟨pc,.wait object phase true true .cta⟩ :: (X.tr g).drop stop)
    (hCredit : ∀ ok, Scores.creditAcquired ⟨pc,.wait object phase ok true .cta⟩ = false)
    (hScore : ∀ ok, scoreAcquired ⟨pc,.wait object phase ok true .cta⟩ = false)
    (h : SoftmaxCounts X g start tc bars elects notices credits scores) :
    SoftmaxCounts X g stop tc bars elects notices credits scores := by
  have keep {mark : Event → Bool} (hm : ∀ ok, mark ⟨pc,.wait object phase ok true .cta⟩ = false) :=
    repeatedScorePollKeepsCount hStart hStop hTrace hm
  exact ⟨(keep (fun _ => rfl)).trans h.1,(keep (fun _ => rfl)).trans h.2.1,
    (keep (fun _ => rfl)).trans h.2.2.1,(keep (fun _ => rfl)).trans h.2.2.2.1,
    (keep hCredit).trans h.2.2.2.2.1,(keep hScore).trans h.2.2.2.2.2⟩

/-- A lane at the head of the biased loop for a given repeated visit (visit one is the first
repeated visit). The trace has consumed exactly `visit` score generations and `11*visit`
Tensor Memory collectives. -/
structure BiasedLoopHead (p : Params) (l : Launch) (X : Execution) (g : Nat) (warp : Fin 8)
    (visit block floor counter bars elects : Nat) (maximum : Option ℝ) (sum : ℝ) where
  valid : DenominatorValid sum maximum
  cursor : OpeningTripCursor l X g 5032
    (biasedHeadFacts p l g warp visit block maximum sum floor counter)
  scores : okPolls (Scores.scoreReadyObject l (g/l.block) (stageOf warp))
    ((X.tr g).take cursor.pos) = visit
  counts : SoftmaxCounts X g cursor.pos (11*visit) bars elects visit (visit+1) visit
  blocks : Nat
  split : Nat
  pastTile : Nat
  geometry : Holds cursor.ready.regs (loopGeometry blocks split pastTile)
  bounds : blocks < 2^31 ∧ split < blocks

private theorem keptStable (p : Params) (l : Launch) (g visit : Nat) (maximum : Option ℝ)
    (sum : ℝ) (floor counter : Nat) :
    ∀ x ∈ biasedHeadKept p l g visit maximum sum floor counter,
      x.1 ∉ biasedScoreSetupWrites 5032 77 ∧ x.1 ≠ 9754 := by
  intro x hx
  simp only [biasedHeadKept,openingDenominatorRegisters,List.cons_append,
    List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by dsimp only; decide +kernel,by dsimp only; decide⟩

/-- The opening denominator of a tile whose first repeated visit is biased reaches the
biased loop head of visit one. -/
theorem OpeningDenominatorCursor.biasedLoopHead {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g blocks cap past : Nat} (hw : warpIndex l g < 8)
    (c : OpeningDenominatorCursor p l X g blocks cap past)
    (hBlocks : 0 < blocks) (hSigned : blocks < 2^31) (hCap : 0 < cap)
    (hCapSigned : cap < 2^31) (hPast : past+256 < 2^31)
    (hBias : firstBiasedRepeats blocks cap ≠ 0)
    (hScores : okPolls (Scores.scoreReadyObject l (g/l.block) (stageOf ⟨warpIndex l g,hw⟩))
      ((X.tr g).take c.cursor.pos) = 1)
    (hNotices : ((X.tr g).take c.cursor.pos).countP Scores.publishesStats = 1)
    (hCredits : ((X.tr g).take c.cursor.pos).countP Scores.creditAcquired = 2)
    (hScoreCount : ((X.tr g).take c.cursor.pos).countP scoreAcquired = 1) :
    ∃ head : BiasedLoopHead p l X g ⟨warpIndex l g,hw⟩ 1 (blocks-1) (past/128)
        (2^32-(blocks-firstPlainSplit blocks cap)) (warpBars X g c.cursor.pos)
        (elections X g c.cursor.pos) c.maximum c.sum,
      head.cursor.pos = c.cursor.pos ∧ head.cursor.ending = c.cursor.ending ∧
      head.blocks = blocks ∧ head.split = firstPlainSplit blocks cap ∧ head.pastTile = past := by
  let split := firstPlainSplit blocks cap
  obtain ⟨s,hLocal,hs,hAbi⟩ := c.enterLoops hp hBlocks hSigned hCap hCapSigned hPast
  have hBiasedHead : At s 5032 (firstBiasedFacts blocks split past c.maximum c.sum) := by
    simpa only [hBias,↓reduceIte] using hs
  have hState (x : Nat × Value) (hx : x ∈ firstBiasedFacts blocks split past c.maximum c.sum) :=
    holds_mem hBiasedHead.2.2.2.2 hx
  have hHead : At s 5032 (biasedHeadFacts p l g ⟨warpIndex l g,hw⟩ 1 (blocks-1) c.maximum c.sum
      (past/128) (2^32-(blocks-split))) := by
    refine hBiasedHead.mono ⟨hAbi.1,hAbi.2.1,hState (7253,b32 1) ?_,
      hState (7249,b32 (blocks-1)) ?_,(holds_append ..).mpr ⟨hAbi,?_⟩⟩
    · simp [firstBiasedFacts,firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable]
    · simp [firstBiasedFacts,firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable]
    · refine ⟨hState (7251,scoreValue c.maximum) ?_,hState (7257,fl c.sum) ?_,
        hState (1361,b32 (past/128)) ?_,hState (7258,b32 1) ?_,hState (7250,b32 1) ?_,
        hState (7248,b32 (2^32-(blocks-split))) ?_,trivial⟩
      all_goals simp [firstBiasedFacts,firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable]
  refine ⟨⟨c.valid,
    ⟨c.cursor.pos,c.cursor.before,s,c.cursor.ending,c.cursor.positive,c.cursor.bounded,
      c.cursor.released,hHead,c.cursor.recorded,c.cursor.remaining,
      c.cursor.localSteps.trans hLocal⟩,hScores,
      ⟨by simpa using c.tensors,rfl,rfl,hNotices,hCredits,hScoreCount⟩,blocks,split,past,
      ⟨hState (1226,b32 blocks) ?_,hState (1229,b32 (blocks-1)) ?_,
        hState (1225,b32 (past+256)) ?_,hState (1360,b32 (past/128)) ?_,
        hState (1359,b32 split) ?_,
        trivial⟩,⟨hSigned,by unfold split firstPlainSplit; omega⟩⟩,rfl,rfl,rfl,rfl,rfl⟩
  all_goals simp [firstBiasedFacts,firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable]

/-- The score-ready facts of a returned biased lane. -/
def biasedReturnedFacts (p : Params) (l : Launch) (g : Nat) (stage : Fin 2) (visit block : Nat)
    (maximum : Option ℝ) (sum : ℝ) (floor counter : Nat) : List (Nat × Value) :=
  biasedScoreReadyFacts l g stage (visit%2) block
    (biasedHeadKept p l g visit maximum sum floor counter)

/-- A head lane whose score generation is ready (when still pending) returns from the
score acquire with the score-ready facts and unchanged tensor count. -/
structure BiasedScoreReturned (p : Params) (l : Launch) (X : Execution) (g : Nat)
    (warp : Fin 8) (visit block floor counter bars elects : Nat) (maximum : Option ℝ)
    (sum : ℝ) where
  head : BiasedLoopHead p l X g warp visit block floor counter bars elects maximum sum
  returned : RepeatedScoreCursor l X g .biased (stageOf warp) (visit%2)
    (biasedReturnedFacts p l g (stageOf warp) visit block maximum sum floor counter)
  after : head.cursor.pos ≤ returned.index
  ending : returned.cursor.ending = head.cursor.ending
  scores : okPolls (Scores.scoreReadyObject l (g/l.block) (stageOf warp))
    ((X.tr g).take returned.cursor.pos) = visit+1
  counts : SoftmaxCounts X g returned.cursor.pos (11*visit) bars elects visit (visit+1)
    (visit+1)

theorem BiasedLoopHead.scoreReturnedOfPending {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g visit block floor counter bars elects : Nat} {maximum : Option ℝ} {sum : ℝ}
    (hg : g < l.threads) {warp : Fin 8} (hw : warp.val = warpIndex l g)
    (c : BiasedLoopHead p l X g warp visit block floor counter bars elects maximum sum)
    (hReady : let loc := Scores.scoreReadyObject l (g/l.block) (stageOf warp)
      okPolls loc (X.tr g) = visit → OpeningPollReady X loc (visit%2)) :
    Nonempty (BiasedScoreReturned p l X g warp visit block floor counter bars elects maximum
      sum) := by
  let facts := biasedHeadKept p l g visit maximum sum floor counter
  have hStable := keptStable p l g visit maximum sum floor counter
  obtain ⟨u,hOrder,hEnd,trace⟩ := biasedScoreReturnOfPending hp hMax hg warp (visit%2) block
    (Nat.mod_lt _ (by decide)) facts (fun x hx => (hStable x hx).1) (fun x hx => (hStable x hx).2)
    c.cursor (fun h => hReady (h.trans c.scores))
  let loc := Scores.scoreReadyObject l (g/l.block) (stageOf warp)
  let poll (ok : Bool) := Event.mk (waitSite (qkWaitSite .biased)).pc
    (.wait loc (visit%2) ok true .cta)
  let window := List.replicate (u.index-c.cursor.pos) (poll false) ++ [poll true]
  have size : c.cursor.pos+window.length = u.cursor.pos := by
    have := u.position
    simp [window]
    omega
  have cut : (X.tr g).drop c.cursor.pos = window ++ (X.tr g).drop u.cursor.pos := by
    simpa [window,poll,loc] using trace
  have step : okPolls loc ((X.tr g).take u.cursor.pos) =
      okPolls loc ((X.tr g).take c.cursor.pos)+1 := by
    rw [← size,List.take_add,cut,List.take_append_length]
    simp [okPolls,window,poll,List.countP_append,List.countP_replicate,okPoll,sourceWaitSuccess]
  have polls := step.trans (congrArg (·+1) c.scores)
  have keep {mark : Event → Bool} (hm : ∀ ok, mark (poll ok) = false) :=
    repeatedScorePollKeepsCount hOrder u.position trace hm
  have hStage : (stageOf warp).val = warpIndex l g/4 := by rw [← hw]; rfl
  refine ⟨⟨c,u,hOrder,hEnd,polls,(keep (fun _ => rfl)).trans c.counts.1,
    (keep (fun _ => rfl)).trans c.counts.2.1,(keep (fun _ => rfl)).trans c.counts.2.2.1,
    (keep (fun _ => rfl)).trans c.counts.2.2.2.1,
    (keep (fun ok => by cases ok <;> rfl)).trans c.counts.2.2.2.2.1,?_⟩⟩
  rw [← scorePollCursor hp hMax.1 (stageOf warp) hStage]
  exact polls

/-- The score operand cursor of a returned lane. -/
noncomputable def BiasedScoreReturned.loadInput {p : Params} {l : Launch} {X : Execution}
    {g : Nat} {warp : Fin 8} {visit block floor counter bars elects : Nat} {maximum : Option ℝ}
    {sum : ℝ}
    (row : BiasedScoreReturned p l X g warp visit block floor counter bars elects maximum sum) :
    OpeningTripCursor l X g (scorePc .biased 0) (roundScoreFacts l g (stageOf warp) .biased) := by
  let c := row.returned.cursor
  refine ⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,c.checkpoint.mono ?_,
    c.recorded,c.remaining,c.localSteps⟩
  exact (holds_append ..).mp ((holds_append ..).mp c.checkpoint.2.2.2.2).1 |>.2

/-- All lanes of a warp whose scores returned load the four score quarters. -/
theorem warpBiasedScoresOfReturned {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {lead visit : Nat} {warp : Fin 8}
    {block floor counter : Nat → Nat} {bars elects : Nat} {maximum : Nat → Option ℝ}
    {sum : Nat → ℝ}
    (rows : ∀ g, SameWarp l lead g → BiasedScoreReturned p l X g warp visit (block g) (floor g)
      (counter g) bars elects (maximum g) (sum g)) :
    ∀ g (peer : SameWarp l lead g), Nonempty (PackedScorePrefix l X g .biased (stageOf warp) 4
      (rows g peer).loadInput) := by
  apply warpRepeatedScoresOfFootprint hp hMax frame
    (Progress.syncGuarded hp hMax.1 (frame.metadataProtected hp).1)
    (Mma.actualMmaLayoutInjective hMax.1) lead (11*visit) .biased (stageOf warp)
    (fun g peer => (rows g peer).loadInput)
  · intro g _ q
    exact List.mem_ofFn.mpr ⟨q,rfl⟩
  · intro g peer
    exact (rows g peer).counts.1
  · intro g peer q k hk v last
    obtain ⟨_,source,_⟩ := last
    exact Safety.tensorWroteWordBytes hp hMax.1 source

/-- After the four loads the lane has completed exactly `visit` Bias rendezvous. -/
theorem BiasedScoreReturned.biasRankAfterLoads {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g visit block floor counter bars elects : Nat} {maximum : Option ℝ} {sum : ℝ}
    {warp : Fin 8} (hw : warp.val = warpIndex l g)
    (row : BiasedScoreReturned p l X g warp visit block floor counter bars elects maximum sum)
    (c : PackedScorePrefix l X g .biased (stageOf warp) 4 row.loadInput) :
    observedBarrierOrdinal X (g,c.cursor.pos) (11+(stageOf warp).val) = visit := by
  have hw8 : warpIndex l g < 8 := hw ▸ warp.isLt
  have hStage : warpIndex l g/4 = (stageOf warp).val := by rw [← hw]; rfl
  have first := c.score 0 (by decide)
  change X.get (g,row.loadInput.pos) = some ⟨scorePc .biased 0,
    .tc (.ld (scoreAddress l g (stageOf warp) 0) (c.words 0) .s32x32b)⟩ at first
  have visits := Scores.scoreLoadExactCursor hp hX (stageOf warp) hw8 hStage .biased 0 first
  have rank := biasedScoreWindowEqualsProbabilityOrdinal hp hX (stageOf warp) hw8 hStage first
    (by decide : 5112 ≤ scorePc .biased 0) (by decide : scorePc .biased 0 ≤ 5181)
  have packedRank := c.keepsOtherCount (Execution.isBarId (11+(stageOf warp).val)) (by
    rintro ⟨site,kind⟩ h
    cases kind <;> first | rfl | cases h)
  change observedBarrierOrdinal X (g,c.cursor.pos) _ =
    observedBarrierOrdinal X (g,row.loadInput.pos) _ at packedRank
  have scores : okPolls (Scores.scoreReadyObject l (g/l.block) (stageOf warp))
      ((X.tr g).take row.loadInput.pos) = visit+1 := row.scores
  omega

end PTX.Kernels.TmlFa4Fwd.Softmax
