-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedLoopHead
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasAcquireInput
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasStageAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue Thread Correction

/-- The head registers carried through the score loads and the Bias wait. -/
def biasedBiasFacts (p : Params) (l : Launch) (g visit block : Nat) (maximum : Option ℝ)
    (sum : ℝ) (floor counter : Nat) : List (Nat × Value) :=
  (7249,b32 ((block+(2^32-1))%2^32)) :: (7253,b32 (visit%2)) ::
    biasedHeadKept p l g visit maximum sum floor counter

/-- The actual Bias acquire of a repeated biased visit, with the packed score words. -/
structure BiasedBiasRow (p : Params) (l : Launch) (X : Execution) (g : Nat) (warp : Fin 8)
    (visit block floor counter bars elects : Nat) (maximum : Option ℝ) (sum : ℝ) where
  row : BiasedScoreReturned p l X g warp visit block floor counter bars elects maximum sum
  scores : PackedScorePrefix l X g .biased (stageOf warp) 4 row.loadInput
  index : Nat
  cursor : OpeningTripCursor l X g 5184
    ((3965,b32 (waitLoc l g (stageOf warp) 5).addr)::(7250,b32 (visit%2))::
      (repeatedBiasPackFrame scores.words ++
        biasedBiasFacts p l g visit block maximum sum floor counter))
  acquired : X.get (g,index) =
    some ⟨5181,.wait (waitLoc l g (stageOf warp) 5) (visit%2) true true .cta⟩
  position : cursor.pos = index+1
  ending : cursor.ending = row.loadInput.ending
  rank : observedBarrierOrdinal X (g,cursor.pos) (11+(stageOf warp).val) = visit
  counts : SoftmaxCounts X g cursor.pos (11*visit+4) bars elects visit (visit+1) (visit+1)

private theorem biasFactsPreserved (p : Params) (l : Launch) (g visit block : Nat)
    (maximum : Option ℝ) (sum : ℝ) (floor counter : Nat) :
    ∀ x ∈ biasedBiasFacts p l g visit block maximum sum floor counter,
      (∀ q : Fin 4, RepeatedScorePreserved .biased q x.1) ∧ x.1 ≠ 3965 ∧ x.1 ≠ 9755 := by
  intro x hx
  simp only [biasedBiasFacts,biasedHeadKept,openingDenominatorRegisters,List.cons_append,
    List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only <;> unfold RepeatedScorePreserved <;> decide

theorem BiasedScoreReturned.biasOfPending {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g visit block floor counter bars elects : Nat} {maximum : Option ℝ} {sum : ℝ}
    {warp : Fin 8} (hg : g < l.threads) (hw : warp.val = warpIndex l g)
    (row : BiasedScoreReturned p l X g warp visit block floor counter bars elects maximum sum)
    (scores : PackedScorePrefix l X g .biased (stageOf warp) 4 row.loadInput)
    (ready : (X.tr g).countP (Execution.isBarId (11+(stageOf warp).val)) = visit →
      ∀ {t}, Run kernel Assumptions.all l g {} (X.tr g) (some t) →
        OpeningPollReady X (waitLoc l g (stageOf warp) 5) (visit%2)) :
    Nonempty (BiasedBiasRow p l X g warp visit block floor counter bars elects maximum sum) := by
  have rank := row.biasRankAfterLoads hp hMax.1 hw scores
  have regs := row.returned.cursor.checkpoint.2.2.2.2
  change Holds _ (biasedScoreReadyFacts l g (stageOf warp) (visit%2) block
    (biasedHeadKept p l g visit maximum sum floor counter)) at regs
  have setup := ((holds_append ..).mp ((holds_append ..).mp regs).1).1
  have facts : Holds row.loadInput.ready.regs
      (biasedBiasFacts p l g visit block maximum sum floor counter) :=
    ⟨setup.2.2.2.1,setup.2.1,((holds_append ..).mp regs).2⟩
  have base : row.loadInput.ready.regs 4037 = some (b32 (l.sharedBase+8*(stageOf warp).val)) :=
    setup.2.2.1
  have parity : row.loadInput.ready.regs 7250 = some (b32 (visit%2)) :=
    holds_mem facts (by simp [biasedBiasFacts,biasedHeadKept])
  have kept := biasFactsPreserved p l g visit block maximum sum floor counter
  obtain ⟨i,c,he,le,pos,ending,bar,trace⟩ := scores.biasedAcquireOfPending hp hMax hg
    (Nat.mod_lt _ (by decide)) base parity (fun h {_} run => ready (h.trans rank) run) _ facts
    (fun x hx => (kept x hx).1) (fun x hx => (kept x hx).2)
  have packed : SoftmaxCounts X g scores.cursor.pos (11*visit+4) bars elects visit
      (visit+1) (visit+1) := by
    have other {mark : Event → Bool} (hm : ∀ e, mark e = true → isTcColl e = false) :=
      scores.keepsOtherCount mark hm
    have h := row.counts
    refine ⟨?_,(other ?_).trans h.2.1,(other ?_).trans h.2.2.1,(other ?_).trans h.2.2.2.1,
      (other ?_).trans h.2.2.2.2.1,(other ?_).trans h.2.2.2.2.2⟩
    · rw [scores.ordinal]
      change _ + 1*4 = _
      rw [show row.loadInput.pos = row.returned.cursor.pos from rfl,h.1]
    all_goals
      rintro ⟨site,kind⟩ hm
      cases kind <;> first | rfl | cases hm
  exact ⟨⟨row,scores,i,c,he,pos,ending,bar.trans rank,
    SoftmaxCounts.ofPolls le pos trace (fun ok => by cases ok <;> rfl)
      (fun ok => by cases ok <;> rfl) packed⟩⟩

private def survivesBiasVectors (r : Nat) : Prop :=
  r ∉ [4166,4167,4168,4169,4170] ∧ (∀ i, biasVectorKeeps true i r) ∧
    r ≠ biasBarReg true ∧ r ∉ biasReleaseWritten true

private theorem scorePairSurvives (q : Fin 4) (k : Fin 16) :
    survivesBiasVectors (repeatedScorePairReg .biased q k.val) := by
  have checked : ∀ (a : Fin 4) (b : Fin 16),
      survivesBiasVectors (repeatedScorePairReg .biased a b.val) := by
    unfold survivesBiasVectors biasVectorKeeps
    decide +kernel
  exact checked q k

/-- The score words and loop registers survive the Bias vector window. -/
theorem BiasedBiasRow.vectorLane {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g visit block floor counter bars elects : Nat} {maximum : Option ℝ} {sum : ℝ}
    {warp : Fin 8} (hw : warp.val = warpIndex l g) {stage : Fin 2} (hs : stageOf warp = stage)
    (r : BiasedBiasRow p l X g warp visit block floor counter bars elects maximum sum) :
    ∃ a : RepeatedBiasAcquireLane l X g stage visit
      (Scores.repeatedBiasFencePack p l g warp ++ (repeatedBiasPackFrame r.scores.words ++
        biasedBiasFacts p l g visit block maximum sum floor counter)),
      a.warp = warp ∧ a.cursor.pos = r.cursor.pos ∧ a.cursor.ending = r.cursor.ending := by
  subst hs
  let facts := repeatedBiasPackFrame r.scores.words ++
    biasedBiasFacts p l g visit block maximum sum floor counter
  let c := r.cursor
  let cursor : OpeningTripCursor l X g 5184 facts :=
    ⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,
      c.checkpoint.mono c.checkpoint.2.2.2.2.2.2,c.recorded,c.remaining,c.localSteps⟩
  have safe (x : Nat × Value) (hx : x ∈ facts) : survivesBiasVectors x.1 := by
    rcases List.mem_append.mp hx with packed | kept
    · obtain ⟨q,_,h⟩ := List.mem_flatMap.mp packed
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp h
      exact scorePairSurvives q k
    · simp only [biasedBiasFacts,biasedHeadKept,openingDenominatorRegisters,List.cons_append,
        List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at kept
      rcases kept with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        dsimp only <;> unfold survivesBiasVectors biasVectorKeeps <;> decide +kernel
  obtain ⟨lane,hWarp,_,hPos,hEnd⟩ := repeatedBiasAcquireLaneOfActual hp hX warp hw
    cursor r.acquired r.position safe
  have rank : observedBarrierOrdinal X (g,cursor.pos) (11+(stageOf warp).val) = visit := r.rank
  exact ⟨{ lane with rank := lane.rank.trans rank },hWarp,hPos,hEnd⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
