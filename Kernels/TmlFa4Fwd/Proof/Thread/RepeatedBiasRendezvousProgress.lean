-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AffineCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasVectorProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasRendezvousProgress
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleBiasWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction Thread

/-- The actual repeated Bias reads drive the proxy fence and stage arrival and
leave the unpacked operands and resident frame live at the barrier return. -/
theorem repeatedBiasArrivalOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hFrame : OutputFootprint p X)
    {g : Nat} (hg : g < l.threads) (warp : Fin 8)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g 5184 F)
    (hRow : c.ready.regs 3976 = some (b32 (repeatedBiasRowBase l g)))
    (hStage : c.ready.regs 3977 = some (b32 (repeatedBiasStageOffset warp)))
    (hOther : ∀ j : Fin 14, c.ready.regs (3982+4*j.val) = some (b32 (kvSwizzle
      (repeatedBiasRowBase l g+repeatedBiasStageOffset warp+repeatedVectorDisplacement j))))
    (hStable : ∀ x ∈ F, x.1 ∉ [4166,4167,4168,4169,4170])
    (hVectorKeep : ∀ x ∈ F, ∀ i, biasVectorKeeps true i x.1)
    (hBarKeep : ∀ x ∈ F, x.1 ≠ biasBarReg true)
    (hFence : ∀ x ∈ biasFenceFacts l g warp true, x ∈ F) :
    ∃ bias : Nat → Option ℝ, ∃ arrived : AffineCursor l X g (biasFencePc true+3),
      arrived.pos = c.pos+66 ∧ arrived.ending = c.ending ∧
      X.get (g,c.pos+64) = some
        ⟨biasFencePc true,.fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g,c.pos+65) = some
        ⟨biasFencePc true+2,.bar (11+(stageOf warp).val) (some 128) .sync⟩ ∧
      At arrived.ready (biasFencePc true+3) (biasKeep l g warp true) ∧
      Holds arrived.ready.regs F ∧
      ∀ i : Fin 16,
        let words := fun k => biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1))
        BiasWordReads l X true i g (c.pos+4*i.val)
          (biasVectorBase l g (stageOf warp) true i) words ∧
        BiasUnpacked true i arrived.ready words := by
  obtain ⟨words,t,hPosition,hEnding,hData⟩ :=
    repeatedBiasVectorsOfMaximal hp hMax hGuard hFrame hg warp c hRow hStage hOther
      hStable hVectorKeep
  let cut : OpeningLaneCursor l X g (biasFencePc true) F t.ending :=
    ⟨t.pos,t.before,t.ready,t.positive,t.bounded,t.released,t.recorded,t.remaining,
      t.localSteps,t.checkpoint⟩
  obtain ⟨u,hProxy,hArrival,hAt,hRun,hTail,hRegs⟩ := biasRendezvousOfMaximal hp hMax hg warp
    true cut (by
      unfold biasFenceFacts biasKeep
      repeat' apply And.intro
      all_goals first | trivial | exact holds_mem t.checkpoint.2.2.2.2 (hFence _ (by simp [
        biasFenceFacts,biasKeep])))
  have hLen' := len_of_get hArrival
  have hLen : cut.pos+1 < (X.tr g).length := hLen'
  have hCut : cut.pos = c.pos+64 := hPosition
  rw [hCut] at hProxy hArrival hLen hRun hTail
  let arrived : AffineCursor l X g (biasFencePc true+3) :=
    ⟨c.pos+66,u,u,c.ending,by omega,by omega,hAt.mono (by simp),by
      simpa only [Nat.add_assoc] using hRun,by
      simpa only [Nat.add_assoc,hEnding] using hTail,.refl⟩
  have hLive : Holds u.regs F := by
    apply Epilogue.holdsSchedulerFrame (regs := F.map Prod.fst) t.checkpoint.2.2.2.2
    · intro r hr
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
      exact hRegs x.1 (hBarKeep x hx)
    · exact fun _ hx => List.mem_map_of_mem hx
  have hCanonical (i : Fin 16) (k : Nat) (hk : k < 4) :
      ∃ lo hi : Option ℝ, words i k = biasLoadWord lo hi := by
    obtain ⟨bs,hGet,hRebuild⟩ := (hData i).1 k hk
    obtain ⟨lo,hi,hWord⟩ := Scores.repeatedBiasWordShapeInPrefix hp hMax.1 hFrame hGet
    exact ⟨lo,hi,Except.ok.inj (hRebuild.symm.trans hWord)⟩
  classical
  choose lo hi hWord using hCanonical
  let bias (col : Nat) :=
    if hv : col/8 < 16 ∧ col%8/2 < 4 then
      if col%2 = 0 then lo ⟨col/8,hv.1⟩ (col%8/2) hv.2
      else hi ⟨col/8,hv.1⟩ (col%8/2) hv.2
    else none
  have hWordEq (i : Fin 16) (k : Nat) (hk : k < 4) :
      words i k = biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1)) := by
    have low : (8*i.val+2*k)/8 = i.val ∧ (8*i.val+2*k)%8/2 = k ∧
        (8*i.val+2*k)%2 = 0 := by omega
    have high : (8*i.val+2*k+1)/8 = i.val ∧ (8*i.val+2*k+1)%8/2 = k ∧
        (8*i.val+2*k+1)%2 ≠ 0 := by omega
    have hValid : i.val < 16 ∧ k < 4 := ⟨i.isLt,hk⟩
    simp only [bias,low.1,low.2.1,low.2.2,high.1,high.2.1,high.2.2,
      dite_eq_left hValid,ite_true,ite_false]
    exact hWord i k hk
  refine ⟨bias,arrived,rfl,rfl,hProxy,by simpa only [Nat.add_assoc] using hArrival,hAt,hLive,?_⟩
  intro i
  constructor
  · intro k hk
    obtain ⟨bs,hGet,hRebuild⟩ := (hData i).1 k hk
    exact ⟨bs,hGet,hRebuild.trans (congrArg Except.ok (hWordEq i k hk))⟩
  · intro k hk
    have hLeft : (biasUnpackRegs true i k).1 ≠ biasBarReg true := by
      have hI := i.isLt
      simp only [biasUnpackRegs,biasUnpackTop,biasBarReg,ite_true]
      omega
    have hRight : (biasUnpackRegs true i k).2 ≠ biasBarReg true := by
      have hI := i.isLt
      simp only [biasUnpackRegs,biasUnpackTop,biasBarReg,ite_true]
      omega
    dsimp only
    rw [← hWordEq i k hk]
    exact ⟨(hRegs _ hLeft).trans ((hData i).2 k hk).1,
      (hRegs _ hRight).trans ((hData i).2 k hk).2⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
