-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
public import Kernels.TmlFa4Fwd.Proof.SoftmaxStats
import Kernels.TmlFa4Fwd.Proof.SoftmaxTerminalPublish
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationValue
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Step.PlainWriteProgress
import Lemmas.Tmem.TmemPairHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Correction

private theorem statsStoreOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8)
    (warp : Fin 8) (site : Fin 4) {F : List (Nat × Value)} {word : Value}
    (hVal : word.bytes = 4) (hA : ((statsStore site).base,b32 (statsBase l g warp)) ∈ F)
    (hV : ((statsStore site).word,word) ∈ F)
    (c : OpeningTripCursor l X g (statsStore site).pc F) :
    X.Writes (g,c.pos) (statsAcc l g warp site) word.toBytes ∧
      ∃ nextC : OpeningTripCursor l X g ((statsStore site).pc+1) F, nextC.pos = c.pos+1 := by
  have hOut := statsStoreOut hp warp site
    (c.checkpoint.mono ⟨holds_mem c.checkpoint.2.2.2.2 hA,
      holds_mem c.checkpoint.2.2.2.2 hV,trivial⟩) hVal
  have hn := Next.mk c.localSteps hOut
  obtain ⟨he,hPrefix,hTail⟩ := Step.plain_write_of_maximal hMax hg (a := statsAcc l g warp site)
    rfl hn c.recorded c.remaining c.positive c.bounded c.released (by
      intro cta req hReq hEq
      have hCovered := (hMax.1.tmemPair.1 cta).1 req hReq
      have hActor := (Tmem.Pair.WarpRequest.event_props hCovered.2.2 0).2.1
      have hWarp := Thread.allocatorWarp hp hMax.1 hReq
      have hThread : (req.own.event l 0).1 = g := congrArg Prod.fst hEq
      rw [hThread,hWarp] at hActor
      change warpIndex l g = 12 at hActor
      omega) (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  have hEvent : X.get (g,c.pos) = some
      ⟨(statsStore site).pc,.wr (statsAcc l g warp site) word.toBytes⟩ :=
    by simpa only [c.checkpoint.1] using he
  refine ⟨⟨_,hEvent⟩,
    ⟨c.pos+1,next c.ready,next c.ready,c.ending,Nat.succ_pos _,len_of_get he,?_,
      c.checkpoint.next,hPrefix,hTail,.refl⟩,rfl⟩
  exact releasedIfLast he (by simp [Kind.resume])

/-- The reached terminal check forces both row-specific stores and their final arrival
even when the original execution prefix ends before the stores. -/
theorem terminalStatisticsPublicationOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (warp : Fin 8) (hWarp : warp.val = warpIndex l g)
    {sum maximum : Value} (hSum : sum.bytes = 4) (hMaxWord : maximum.bytes = 4)
    (c : OpeningTripCursor l X g 7605 [(1215,b32 (laneOf l g)),(1062,b32 warp.val),
      (2535,b32 l.sharedBase),(7257,sum),(7256,maximum),(5127,b32 (3+warp.val))]) :
    X.Writes (g,c.pos) (statsAcc l g warp 2) sum.toBytes ∧
      X.Writes (g,c.pos+1) (statsAcc l g warp 3) maximum.toBytes ∧
      Thread.Scores.Publishes X (g,c.pos+2) .final := by
  let F := [(5814,b32 (statsBase l g warp)),(7257,sum),(7256,maximum),(5127,b32 (3+warp.val))]
  have hw : warpIndex l g < 8 := hWarp ▸ warp.isLt
  obtain ⟨u,hLocal,hu⟩ := terminalStatsReadyFromDrain hp warp hWarp c.checkpoint
  let ready : OpeningTripCursor l X g 7614 F :=
    ⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hu,c.recorded,c.remaining,
      c.localSteps.trans (run_rtg hLocal)⟩
  obtain ⟨hStored,second,hSecond⟩ := statsStoreOfMaximal hp hMax hg hw warp 2 hSum
    (by simp [F,statsStore]) (by simp [F,statsStore]) ready
  obtain ⟨hStored',bar,hBar⟩ := statsStoreOfMaximal hp hMax hg hw warp 3 hMaxWord
    (by simp [F,statsStore]) (by simp [F,statsStore]) second
  obtain ⟨he,_,_⟩ := statsArrivalOfMaximal hp none warp hg bar.positive bar.bounded
    (bar.checkpoint.mono ⟨holds_mem bar.checkpoint.2.2.2.2 (by simp [F]),trivial⟩)
    bar.recorded bar.localSteps bar.remaining (fun h => ⟨X,hMax,rfl,bar.released h⟩)
  have hPos : bar.pos = c.pos+2 := by
    rw [hBar,hSecond]
  rw [hPos] at he
  rw [hSecond] at hStored'
  exact ⟨hStored,hStored',⟨_,he,rfl⟩⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
