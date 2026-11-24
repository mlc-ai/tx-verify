-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainLogits
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRecurringScoreValue
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedScoreCommit
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedMax
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.AllScoreLoadWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma PTX.Flow Prologue Epilogue Thread Thread.Scores

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem plainScoreWordOfLaunchInputs (hFrame : OutputFootprint p X) {g pos batch : Nat}
    {stage : Fin 2} (q : Fin 4) (k : Fin 32) {values : List Value}
    (hs : warpIndex l g/4 = stage.val)
    (he : X.get (g,pos) =
      some ⟨scorePc .unbiased q,.tc (.ld (scoreAddress l g stage q) values .s32x32b)⟩)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    let co := assignedCoordinates p batch (g/l.block)
    let visit := probabilityOrdinal l X (g/l.block) stage 0 (g,pos)
    values[k.val]? = some (.float .f32
      (firstScoreDot p l g batch co.2 (p.qOffset batch+256*co.1+128*stage.val)
        (128*(Mma.trips p batch co.1-1-visit)) q k)) := by
  obtain ⟨other,actual,hRole,hb',hLo',hHi',hWords⟩ :=
    scoreLoadWordsOfLaunch hp hX hFrame .unbiased q he
  have hStage : other = stage := Fin.ext (hRole.symm.trans hs)
  subst other
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hBatch := (hUnique actual ⟨hb',hLo',hHi'⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  exact hBatch ▸ hWords k

/-- The next actual plain score-load sequence yields the packed values on the supplied
run and retains the other live registers until the maximum starts. -/
theorem plainPackedDotsFromLoadsOfFootprint (hCuQ : DrainCuQProtected p X)
    (hFrame : OutputFootprint p X) (warp : Fin 8) {g start batch : Nat} {t : TState}
    (hWarp : warp.val = warpIndex l g) (ht : At t (scorePc .unbiased 0) [])
    (hAddr : ∀ q : Fin 4, t.regs (scoreReg .unbiased q) =
      some (b32 (scoreAddress l g (stageOf warp) q)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop start) none) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ u,
      let stage := stageOf warp
      let co := assignedCoordinates p batch (g/l.block)
      let visit := probabilityOrdinal l X (g/l.block) stage 0 (g,start)
      let dot := fun q k => firstScoreDot p l g batch co.2
        (p.qOffset batch+256*co.1+128*stage.val) (128*(Mma.trips p batch co.1-1-visit)) q k
      At u (repeatedMaxStart false) [] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+8)) none ∧
      (∀ q : Fin 4, X.get (g,start+2*q.val+1) = some ⟨scorePc .unbiased q,.tc .waitLd⟩) ∧
      (∀ n, (∀ q : Fin 4,
        (n < repeatedScoreWordBase .unbiased q ∨ repeatedScoreWordBase .unbiased q+32 ≤ n) ∧
        ∀ i : Fin 16, n ≠ repeatedScorePairReg .unbiased q i.val) → u.regs n = t.regs n) ∧
      (∀ q : Fin 4, ∃ values, X.get (g,start+2*q.val) = some
        ⟨scorePc .unbiased q,.tc (.ld (scoreAddress l g stage q) values .s32x32b)⟩) ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop start).take 8) u ∧
      ∀ (q : Fin 4) (k : Fin 16),
        let lo : Fin 32 := ⟨2*k.val,by have := k.isLt; omega⟩
        let hi : Fin 32 := ⟨2*k.val+1,by have := k.isLt; omega⟩
        u.regs (repeatedScorePairReg .unbiased q k.val) =
          some (.pair (.float .f32 (dot q lo)) (.float .f32 (dot q hi))) := by
  let stage := stageOf warp
  have hs : warpIndex l g/4 = stage.val := by rw [← hWarp]; rfl
  have hBytes (q : Fin 4) (xs : List Value) (_ : (0 : Fin 4) ≤ q)
      (hLoad : X.get (g,start+2*q.val) =
        some ⟨scorePc .unbiased q,.tc (.ld (scoreAddress l g stage q) xs .s32x32b)⟩) :
      ∀ k < 32, (xs.getD k (b32 0)).bytes = 4 := by
    intro k hk
    have hVal := plainScoreWordOfLaunchInputs
      hp hX hFrame q ⟨k,hk⟩ hs hLoad hb hLo hHi
    dsimp only at hVal
    simp [List.getD,hVal,Value.bytes,FloatFmt.bytes]
  obtain ⟨u,hAt,hPacked,hWait,hKeep,hTail,hReach⟩ :=
    repeatedScoreTraceFromWithReach hp .unbiased stage 0 ht (fun q _ => hAddr q)
      hBytes (by simpa only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] using hRun)
  let values (q : Fin 4) := Classical.choose (hPacked q (Fin.zero_le _))
  have hReads (q : Fin 4) := (Classical.choose_spec (hPacked q (Fin.zero_le _))).2
  obtain ⟨banks,hBanks⟩ := observedRepeatedScoreTile hp hX hCuQ .unbiased stage hs values
    (fun q => (hReads q).1) (fun e q => hWait e q (Fin.zero_le _))
  have hOrdinal (q : Fin 4) :
      probabilityOrdinal l X (g/l.block) stage 0 (g,start+2*q.val) =
        probabilityOrdinal l X (g/l.block) stage 0 (g,start) := by
    have h := (banks q 0).seen.generation.symm.trans
      ((congrArg (scoreCommitOrdinal l X (g/l.block) stage) (hBanks q 0)).trans
        (banks 0 0).seen.generation)
    simpa only [repeatedScoreStride,ite_true,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using h
  refine ⟨u,hAt,hTail,(fun q => hWait rfl q (Fin.zero_le _)),?_,?_,?_,?_⟩
  · intro n hn
    exact hKeep n (fun q _ => hn q)
  · intro q
    obtain ⟨xs,_,he,_⟩ := hPacked q (Fin.zero_le _)
    exact ⟨xs,by simpa only [Repeated.round,repeatedScoreStride,ite_true] using he⟩
  · simpa only [repeatedScoreStride,Fin.val_zero,Nat.mul_zero,Nat.add_zero,Nat.sub_zero,
      ite_true,Nat.reduceMul] using hReach
  · intro q k
    have hWord (w : Fin 32) := plainScoreWordOfLaunchInputs hp hX hFrame
      q w hs (hReads q).1 hb hLo hHi
    have hLoWord := hWord ⟨2*k.val,by have := k.isLt; omega⟩
    have hHiWord := hWord ⟨2*k.val+1,by have := k.isLt; omega⟩
    dsimp only at hLoWord hHiWord ⊢
    change (values q)[2*k.val]? = _ at hLoWord
    change (values q)[2*k.val+1]? = _ at hHiWord
    simp only [repeatedScoreStride,ite_true,hOrdinal] at hLoWord hHiWord
    have hPair := (hReads q).2 k.val k.isLt
    change u.regs (repeatedScorePairReg .unbiased q k.val) =
      some (joinValue ((values q).getD (2*k.val) (b32 0))
        ((values q).getD (2*k.val+1) (b32 0))) at hPair
    simpa only [List.getD_eq_getElem?_getD,hLoWord,hHiWord,Option.getD_some,joinValue] using hPair

end PTX.Kernels.TmlFa4Fwd.Softmax
