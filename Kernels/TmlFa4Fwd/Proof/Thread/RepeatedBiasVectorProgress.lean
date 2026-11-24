-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreBiasProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasVectorProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedBiasAddresses
import all Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleBiasWords
import all Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction Thread Thread.Scores

/-- A returning repeated Bias acquire advances through the sixteen actual vectors
and preserves the live packed QK operands at their proxy fence. -/
theorem repeatedBiasVectorsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hFrame : OutputFootprint p X)
    {g : Nat} (hg : g < l.threads) (warp : Fin 8)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g 5184 F)
    (hRow : c.ready.regs 3976 = some (b32 (repeatedBiasRowBase l g)))
    (hStage : c.ready.regs 3977 = some (b32 (repeatedBiasStageOffset warp)))
    (hOther : ∀ j : Fin 14, c.ready.regs (3982+4*j.val) = some (b32 (kvSwizzle
      (repeatedBiasRowBase l g+repeatedBiasStageOffset warp+repeatedVectorDisplacement j))))
    (hStable : ∀ x ∈ F, x.1 ∉ [4166,4167,4168,4169,4170])
    (hVectorKeep : ∀ x ∈ F, ∀ i, biasVectorKeeps true i x.1) :
    ∃ words : Fin 16 → Nat → Value,
      ∃ after : OpeningTripCursor l X g (biasFencePc true) F,
        after.pos = c.pos+64 ∧ after.ending = c.ending ∧
        ∀ i, BiasWordReads l X true i g (c.pos+4*i.val)
          (biasVectorBase l g (stageOf warp) true i) (words i) ∧
          BiasUnpacked true i after.ready (words i) := by
  let stage := stageOf warp
  let base := biasVectorBase l g stage true
  obtain ⟨s,hLocal,hs,hKeep⟩ := repeatedBiasFirstVectorSetupFramed hp g warp
    (c.checkpoint.mono ⟨hRow,hStage,trivial⟩)
  have hBases (i : Fin 16) :
      s.regs (biasReadSite true i).base = some (b32 (base i)) := by
    apply repeatedReadAddressOfRegisters hp (w := warp) i hs.2.2.2.2.1
    intro j
    have hBound := j.isLt
    exact (hKeep _ (by simp; omega)).trans (hOther j)
  let addresses := (List.finRange 16).map fun i => ((biasReadSite true i).base,b32 (base i))
  have hLive : Holds s.regs F := by
    apply Epilogue.holdsSchedulerFrame (regs := F.map Prod.fst) c.checkpoint.2.2.2.2
    · intro r hr
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
      exact hKeep _ (hStable x hx)
    · exact fun _ hx => List.mem_map_of_mem hx
  have hAddrs : Holds s.regs addresses := by
    apply frameOfFacts
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact hBases i
  let start : OpeningLaneCursor l X g (biasReadPc true 0) (addresses ++ F) c.ending :=
    ⟨c.pos,c.before,s,c.positive,c.bounded,c.released,c.recorded,c.remaining,
      c.localSteps.trans (run_rtg hLocal),hs.mono ((holds_append ..).mpr ⟨hAddrs,hLive⟩)⟩
  have hAddress (i : Fin 16) : base i+(biasReadSite true i).offset < 2^32 ∧
      (base i+(biasReadSite true i).offset)%16 = 0 := by
    simpa only [base,biasVectorBase_add] using biasVectorAddressBounds hp g stage i
  let expected (i : Fin 16) (k : Nat) (bs : List (Option Byte)) :=
    X.get (g,start.pos+4*i.val+k) =
      some ⟨biasReadPc true i,.rd (biasReadAcc l g (base i) true i k) bs⟩
  have hData (i : Fin 16) (k : Nat) : ∃ lo hi : Option ℝ, ∀ bs, expected i k bs →
      rebuild 3 bs = .ok (biasLoadWord lo hi) := by
    by_cases h : ∃ bs, expected i k bs
    · obtain ⟨bs,he⟩ := h
      obtain ⟨lo,hi,hWord⟩ := repeatedBiasWordShapeInPrefix hp hMax.1 hFrame
        (show BiasVectorRead X (g,c.pos+4*i.val+k) true i
          (biasReadAcc l g (base i) true i k) bs from he)
      refine ⟨lo,hi,fun bytes hGet => ?_⟩
      have hBytes := (Kind.rd.inj (congrArg Event.kind (Option.some.inj (hGet.symm.trans he)))).2
      exact hBytes.symm ▸ hWord
    · exact ⟨none,none,fun bs hb => (h ⟨bs,hb⟩).elim⟩
  choose lo hi hData using hData
  let words i k := biasLoadWord (lo i k) (hi i k)
  have hFresh (x : Nat × Value) (hx : x ∈ addresses ++ F) (i : Fin 16) :
      biasVectorKeeps true i x.1 := by
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
      have hSafe : ∀ (i j : Fin 16), biasVectorKeeps true i (biasReadSite true j).base := by
        unfold biasVectorKeeps
        decide +kernel
      exact hSafe i j
    · exact hVectorKeep x hx i
  obtain ⟨after,hPos,hRead,_⟩ := biasVectorCursorsOfMaximal hMax hGuard hg true start base words
    (fun i => List.mem_append_left _ (List.mem_map_of_mem (by simp)))
    (fun i => (hAddress i).1) (fun i => (hAddress i).2)
    (fun i k _ => biasLoadWordShape (lo i k) (hi i k))
    (fun i k _ bs => hData i k bs) hFresh
  let last : OpeningTripCursor l X g (biasFencePc true) F :=
    ⟨after.pos,after.before,after.ready,c.ending,after.positive,after.bounded,after.released,
      after.checkpoint.mono ((holds_append ..).mp after.checkpoint.2.2.2.2).2,
      after.recorded,after.continuation,after.localSteps⟩
  exact ⟨words,last,hPos,rfl,hRead⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
