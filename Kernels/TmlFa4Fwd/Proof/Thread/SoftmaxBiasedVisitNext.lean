-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedVisitJoin
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRepeatedAckPending
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank
import all Lemmas.Flow.RecordedCheckpointPath
import all Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScorePollRanks

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue Thread Correction

/-- A repeated update keeps a valid denominator: the old mass is rescaled by a nonnegative
factor, every new weight is nonnegative, and a positive mass has a finite reference. -/
theorem repeatedDenominatorValid {scale : ℝ} {old candidate : Option ℝ} {oldSum : ℝ}
    (hValid : DenominatorValid oldSum old) (scores : Nat → Option ℝ)
    (hBound : ∀ v : EReal, scoreReal candidate ≤ v ↔
      scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (scores i) ≤ v) :
    let chosen := chosenReference scale old candidate
    let ref := chosen.map (scale * ·)
    DenominatorValid (oldSum*maskedRescale (old.map (scale * ·)) ref +
      ∑ i ∈ Finset.range 128, repeatedExpWeight (affineScore scale (-ref.getD 0) (scores i)))
      chosen := by
  intro chosen ref
  have hRescale : 0 ≤ maskedRescale (old.map (scale * ·)) ref := by
    cases old <;> simp [maskedRescale,Real.rpow_nonneg]
  have hWeight (x : Option ℝ) : 0 ≤ repeatedExpWeight x := by
    cases x <;> simp [repeatedExpWeight,Real.rpow_nonneg]
  constructor
  · exact add_nonneg (mul_nonneg hValid.nonnegative hRescale)
      (Finset.sum_nonneg fun i _ => hWeight _)
  · intro hPos
    cases hc : chosen with
    | some x => exact ⟨x,rfl⟩
    | none =>
      exfalso
      have hNotKeep : keepReference scale old candidate = false := by
        cases hk : keepReference scale old candidate
        · rfl
        · have : chosen = old := by simp [chosen,chosenReference,hk]
          cases ho : old with
          | none => simp [keepReference,referenceDelta,ho] at hk
          | some y => rw [this,ho] at hc; cases hc
      have hCand : candidate = none := by
        have : chosen = candidate := by simp [chosen,chosenReference,hNotKeep]
        rw [← this,hc]
      have hBot := (hBound ⊥).mp (by rw [hCand]; exact le_refl _)
      have hOld : old = none := by
        cases ho : old with
        | none => rfl
        | some y =>
          have h := hBot.1
          rw [ho] at h
          exact absurd h (by simp [scoreReal])
      have hScores (i : Nat) (hi : i < 128) : scores i = none := by
        cases hs : scores i with
        | none => rfl
        | some y =>
          have h := hBot.2 i hi
          rw [hs] at h
          exact absurd h (by simp [scoreReal])
      have hZero : oldSum*maskedRescale (old.map (scale * ·)) ref +
          ∑ i ∈ Finset.range 128,
            repeatedExpWeight (affineScore scale (-ref.getD 0) (scores i)) = 0 := by
        rw [hOld]
        simp only [Option.map_none,maskedRescale,Option.elim,mul_zero,zero_add]
        apply Finset.sum_eq_zero
        intro i hi
        rw [hScores i (Finset.mem_range.mp hi)]
        rfl
      rw [hZero] at hPos
      exact lt_irrefl 0 hPos

/-- A lane with the biased loop frame of a visit at the loop head or at the biased exit. -/
structure BiasedLoopAt (p : Params) (l : Launch) (X : Execution) (g : Nat) (warp : Fin 8)
    (pc visit block floor counter bars elects : Nat) (maximum : Option ℝ) (sum : ℝ) where
  valid : DenominatorValid sum maximum
  cursor : OpeningTripCursor l X g pc
    (biasedHeadFacts p l g warp visit block maximum sum floor counter)
  scores : okPolls (Scores.scoreReadyObject l (g/l.block) (stageOf warp))
    ((X.tr g).take cursor.pos) = visit
  counts : SoftmaxCounts X g cursor.pos (11*visit) bars elects visit (visit+1) visit
  blocks : Nat
  split : Nat
  pastTile : Nat
  geometry : Holds cursor.ready.regs (loopGeometry blocks split pastTile)
  bounds : blocks < 2^31 ∧ split < blocks
  maxWord : cursor.ready.regs 7256 = some (scoreValue maximum)

/-- At the loop head this is the head of the next visit. -/
def BiasedLoopAt.head {p : Params} {l : Launch} {X : Execution} {g : Nat} {warp : Fin 8}
    {visit block floor counter bars elects : Nat} {maximum : Option ℝ} {sum : ℝ}
    (c : BiasedLoopAt p l X g warp 5032 visit block floor counter bars elects maximum sum) :
    BiasedLoopHead p l X g warp visit block floor counter bars elects maximum sum :=
  ⟨c.valid,c.cursor,c.scores,c.counts,c.blocks,c.split,c.pastTile,c.geometry,c.bounds⟩

private theorem phaseBit (v : Nat) : (decide (v%2 = 1)).toNat = v%2 := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

private theorem nextPhaseBit (v : Nat) : (!decide (v%2 = 1)).toNat = (v+1)%2 := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h] <;> omega

/-- After the correction credit the biased visit updates its denominator and takes the loop
back edge. The lane reaches the head of the next visit, or the biased exit when the loop
counter reaches its sentinel, with all its counts. -/
theorem BiasedVisitJoin.nextOfPending {p : Params} {l : Launch} {m : Mem0}
    {X₀ X Y : Execution} (hp : Pre p l m) (hMax₀ : Maximal l kernel Assumptions.all m X₀)
    (hMax : Maximal l kernel Assumptions.all m Y) (hTrace : Y.tr = X₀.tr)
    {g : Nat} (hg : g < l.threads) {warp : Fin 8} (hw : warp.val = warpIndex l g)
    {visit block floor counter bars elects start nextBlock : Nat} {old : Option ℝ}
    {oldSum : ℝ} {bias : Nat → Option ℝ} {dot : Nat → ℝ}
    (head : BiasedLoopHead p l X₀ g warp visit block floor counter bars elects old oldSum)
    (J : BiasedVisitJoin p l X Y g warp visit start nextBlock counter bars elects old oldSum
      bias dot)
    (hOrder : head.cursor.pos < J.join.cursor.pos) (hCounter : counter < 2^32)
    (hReady : (Y.tr g).countP Scores.creditAcquired = visit+1 →
      OpeningPollReady Y (waitLoc l g (stageOf warp) Repeated.biased.correctionSite)
        (visit%2)) :
    let scale := abiFloat p.scaleLog2Bits
    let chosen := chosenReference scale old J.candidate
    let ref := chosen.map (scale * ·)
    let mass := oldSum*maskedRescale (old.map (scale * ·)) ref +
      ∑ i ∈ Finset.range 128, repeatedExpWeight (affineScore scale (-ref.getD 0)
        (affineScore (abiFloat p.invScaleBits) (dot i) (bias i)))
    let next := (counter+1)%2^32
    ∃ at' : BiasedLoopAt p l X₀ g warp
      (if next ≠ 2^32-1 then 5032 else (scoreLoopSite .biased).increment+4) (visit+1)
      nextBlock floor next (bars+1) (elects+1) chosen mass,
      at'.blocks = head.blocks ∧ at'.split = head.split ∧ at'.pastTile = head.pastTile := by
  intro scale chosen ref mass next
  have hPhaseLt : visit%2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨index,u,he,hUPos,hUEnd,hU7258,hUCont,hLe,window⟩ :=
    J.join.denominatorOfPending hp hMax hg (visit+1) J.counts.2.2.2.2.1 hReady
  have cont (n : Nat) (hn : n ∈ Repeated.biased.continuationRegs) {v : Value}
      (h : J.join.values n = v) : u.ready.regs n = some v := (hUCont n hn).trans (congrArg some h)
  let phase := decide (visit%2 = 1)
  have hPhaseNat : phase.toNat = visit%2 := phaseBit visit
  obtain ⟨after,hAPos,hAEnd,hA7249,hARes⟩ :=
    repeatedLoopOfDenominatorCursor .biased chosen mass counter hCounter phase phase phase u
      (cont 7256 (by decide) J.maximum) (cont 7248 (by decide) J.counterWord)
      (by rw [hPhaseNat]; exact hU7258)
      (fun _ => by rw [hPhaseNat]; exact cont 7250 (by decide) J.biasPhase)
      (by rw [hPhaseNat]; exact cont 7253 (by decide) J.scorePhase)
  -- the head registers that the loop body never writes
  have hJoinLe : J.join.cursor.pos ≤ index := hLe
  have hLt : head.cursor.pos < u.pos := by omega
  have hUBound : u.pos ≤ (X₀.tr g).length := by rw [← hTrace]; exact u.bounded
  have hURec : Run kernel Assumptions.all l g {} ((X₀.tr g).take u.pos) (some u.before) := by
    rw [← hTrace]; exact u.recorded
  have hPath := traceBetweenLaterIndex hLt hUBound head.cursor.recorded head.cursor.localSteps
    hURec u.localSteps
  have hHeadPc : head.cursor.ready.pc = 5032 := head.cursor.checkpoint.1
  have hKeep := scoreTraceKeepsResidents .biased hPath (by rw [hHeadPc]; decide)
    (by rw [u.checkpoint.1]; decide) (by rw [head.cursor.checkpoint.2.1]; decide)
  have headRegs := head.cursor.checkpoint.2.2.2.2
  have resident (r : Nat) (hr : r ∈ loopResident .biased) {v : Value}
      (h : head.cursor.ready.regs r = some v) : after.ready.regs r = some v :=
    ((hARes r hr).trans (hKeep r hr)).trans h
  have hHeadReg (r : Nat) {v : Value}
      (h : (r,v) ∈ biasedHeadFacts p l g warp visit block old oldSum floor counter) :
      head.cursor.ready.regs r = some v := holds_mem headRegs h
  have hd := @hHeadReg
  have aRegs := after.checkpoint.2.2.2.2
  have aReg (r : Nat) {v : Value} (h : (r,v) ∈ [(7248,b32 next),(7251,scoreValue chosen),
      (7256,scoreValue chosen),(7257,fl mass),(7258,b32 (!phase).toNat),
      (7250,b32 (!phase).toNat),(7253,b32 (!phase).toNat)]) : after.ready.regs r = some v := by
    exact holds_mem aRegs h
  have hNext : (!phase).toNat = (visit+1)%2 := nextPhaseBit visit
  have hFrame : Holds after.ready.regs
      (biasedHeadFacts p l g warp (visit+1) nextBlock chosen mass floor next) := by
    apply frameOfFacts
    intro pair hPair
    simp only [biasedHeadFacts,openingDenominatorRegisters,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hPair
    rcases hPair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact resident 1062 (by decide)
        (hd _ (by simp [biasedHeadFacts,openingDenominatorRegisters,hw]))
    · exact resident 2535 (by decide)
        (hd _ (by simp [biasedHeadFacts,openingDenominatorRegisters,hw]))
    · rw [← hNext]; exact aReg 7253 (by simp)
    · exact (hA7249 rfl).trans (cont 7249 (by decide) J.blockWord)
    · exact resident 1062 (by decide)
        (hd _ (by simp [biasedHeadFacts,openingDenominatorRegisters,hw]))
    · exact resident 2535 (by decide)
        (hd _ (by simp [biasedHeadFacts,openingDenominatorRegisters,hw]))
    · exact resident 5127 (by decide) (hd _ (by simp [biasedHeadFacts,
        openingDenominatorRegisters,hw]))
    · exact resident 7132 (by decide) (hd _ (by simp [biasedHeadFacts,
        openingDenominatorRegisters,hw]))
    · exact resident 1230 (by decide) (hd _ (by simp [biasedHeadFacts,
        openingDenominatorRegisters,hw]))
    · exact aReg 7251 (by simp)
    · exact aReg 7257 (by simp)
    · exact resident 1361 (by decide)
        (hd _ (by simp [biasedHeadFacts,openingDenominatorRegisters,hw]))
    · rw [← hNext]; exact aReg 7258 (by simp)
    · rw [← hNext]; exact aReg 7250 (by simp)
    · exact aReg 7248 (by simp)
  -- the counts of the acknowledgement window
  let credit (ok : Bool) := Event.mk (waitSite Repeated.biased.correctionSite).pc
    (.wait (waitLoc l g (stageOf warp) Repeated.biased.correctionSite) (visit%2) ok true .cta)
  have keep {mark : Event → Bool} (hm : ∀ ok, mark (credit ok) = false) :=
    repeatedScorePollKeepsCount hLe hUPos window hm
  let pollWindow := List.replicate (index-J.join.cursor.pos) (credit false) ++ [credit true]
  have size : J.join.cursor.pos+pollWindow.length = u.pos := by
    simp [pollWindow]
    omega
  have cut : (Y.tr g).drop J.join.cursor.pos = pollWindow ++ (Y.tr g).drop u.pos := by
    simpa [pollWindow,credit] using window
  have creditStep : ((Y.tr g).take u.pos).countP Scores.creditAcquired =
      ((Y.tr g).take J.join.cursor.pos).countP Scores.creditAcquired+1 := by
    rw [← size,List.take_add,cut,List.take_append_length]
    simp [pollWindow,credit,List.countP_append,List.countP_replicate,Scores.creditAcquired]
    decide
  have c := J.counts
  have countsY : SoftmaxCounts Y g u.pos (11*(visit+1)) (bars+1) (elects+1) (visit+1)
      (visit+1+1) (visit+1) :=
    ⟨(keep (fun _ => rfl)).trans (c.1.trans (by ring)),(keep (fun _ => rfl)).trans c.2.1,
      (keep (fun _ => rfl)).trans c.2.2.1,(keep (fun _ => rfl)).trans c.2.2.2.1,
      creditStep.trans (congrArg (·+1) c.2.2.2.2.1),
      (keep (fun ok => by cases ok <;> rfl)).trans c.2.2.2.2.2⟩
  have countsX := SoftmaxCounts.ofTrace hTrace.symm countsY
  have heX : X₀.get (g,index) = Y.get (g,index) := by
    simp only [Execution.get,hTrace]
  let cur : OpeningTripCursor l X₀ g
      (if next ≠ 2^32-1 then 5032 else (scoreLoopSite .biased).increment+4)
      (biasedHeadFacts p l g warp (visit+1) nextBlock chosen mass floor next) :=
    ⟨after.pos,after.before,after.ready,after.ending,after.positive,
      by rw [← hTrace]; exact after.bounded,
      fun h => Prologue.releasedIfLast (heX.trans he) (by simp [Kind.resume])
        (by rw [← hUPos,← hAPos,h]),
      ⟨after.checkpoint.1,after.checkpoint.2.1,after.checkpoint.2.2.1,after.checkpoint.2.2.2.1,
        hFrame⟩,
      by rw [← hTrace]; exact after.recorded,by rw [← hTrace]; exact after.remaining,
      after.localSteps⟩
  have hStage : (stageOf warp).val = warpIndex l g/4 := by rw [← hw]; rfl
  have hCurPos : cur.pos = u.pos := hAPos
  have geo := head.geometry
  refine ⟨⟨repeatedDenominatorValid head.valid _ J.bound,cur,?_,?_,head.blocks,head.split,
    head.pastTile,?_,head.bounds,aReg 7256 (by simp)⟩,rfl,rfl,rfl⟩
  · rw [scorePollCursor hp hMax₀.1 (stageOf warp) hStage,hCurPos]
    exact countsX.2.2.2.2.2
  · rw [hCurPos]
    exact countsX
  · exact ⟨resident 1226 (by decide) geo.1,resident 1229 (by decide) geo.2.1,
      resident 1225 (by decide) geo.2.2.1,resident 1360 (by decide) geo.2.2.2.1,
      resident 1359 (by decide) geo.2.2.2.2.1,trivial⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
