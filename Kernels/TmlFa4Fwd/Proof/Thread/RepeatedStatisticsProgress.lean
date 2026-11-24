-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreNumericsProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalIssueProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationValue
import Lemmas.Step.PlainWriteProgress
import Lemmas.Tmem.TmemPairHistory
import all Kernels.TmlFa4Fwd.Proof.SoftmaxPlainRescale

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Correction Thread.Scores

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (warp : Fin 8)
    (hWarp : warp.val = warpIndex l g) (mode : Repeated) (word : Value) (hWidth : word.bytes = 4)
    {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (statsStore (rescaleStore (mode = .biased))).pc F)
    (hAddress : ((statsStore (rescaleStore (mode = .biased))).base,b32 (statsBase l g warp)) ∈ F)
    (hWord : ((statsStore (rescaleStore (mode = .biased))).word,word) ∈ F)
include hp hMax hg warp hWarp mode word hWidth c hAddress hWord

/-- A runnable repeated rescale word is stored and then announced to correction. -/
theorem rescalePublicationStateOfMaximal (hBar : (5127,b32 (3+warp.val)) ∈ F) :
    StatisticsStore X (g,c.pos) (rescaleStore (mode = .biased))
        (statsAcc l g warp (rescaleStore (mode = .biased))) word.toBytes ∧
      Publishes X (g,c.pos+1) (if mode = .biased then .biased else .plain) ∧
      At (next (next c.ready)) (statsPc (some mode.round)+1) F ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+2)) (some (next (next c.ready))) ∧
      Run kernel Assumptions.all l g (next (next c.ready)) ((X.tr g).drop (c.pos+2)) c.ending := by
  let site := rescaleStore (mode = .biased)
  have hPc : (statsStore site).pc+1 = statsPc (some mode.round) := by cases mode <;> rfl
  have hOut := statsStoreOut hp warp site
    (c.checkpoint.mono ⟨holds_mem c.checkpoint.2.2.2.2 hAddress,
      holds_mem c.checkpoint.2.2.2.2 hWord,trivial⟩) hWidth
  have hn := Next.mk c.localSteps hOut
  obtain ⟨hGet,hRecorded,hRemaining⟩ := Step.plain_write_of_maximal hMax hg
    (a := statsAcc l g warp site) rfl hn c.recorded c.remaining c.positive c.bounded c.released
    (by
      intro cta req hReq hEq
      have hCovered := (hMax.1.tmemPair.1 cta).1 req hReq
      have hActor := (Tmem.Pair.WarpRequest.event_props hCovered.2.2 0).2.1
      have hAllocator := Thread.allocatorWarp hp hMax.1 hReq
      have hThread : (req.own.event l 0).1 = g := congrArg Prod.fst hEq
      rw [hThread,hAllocator] at hActor
      change warpIndex l g = 12 at hActor
      have := warp.isLt
      omega)
    (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  have hAfter : At (next c.ready) (statsPc (some mode.round)) F := hPc ▸ c.checkpoint.next
  have hRelease (hEnd : c.pos+1 = (X.tr g).length) : Step.Released l X g :=
    releasedIfLast hGet (by simp [Kind.resume]) hEnd
  obtain ⟨hNotice,hPast,hTail⟩ := statsArrivalOfMaximal hp (some mode.round) warp hg
    (Nat.succ_pos _) (len_of_get hGet) (hAfter.mono ⟨holds_mem hAfter.2.2.2.2 hBar,trivial⟩)
    hRecorded .refl hRemaining (fun h => ⟨X,hMax,rfl,hRelease h⟩)
  refine ⟨?_,?_,hAfter.next,hPast,hTail⟩
  · simpa only [StatisticsStore,c.checkpoint.1] using hGet
  · cases mode
    · exact ⟨_,hNotice,rfl⟩
    · exact ⟨_,hNotice,rfl⟩

end

end PTX.Kernels.TmlFa4Fwd.Softmax
