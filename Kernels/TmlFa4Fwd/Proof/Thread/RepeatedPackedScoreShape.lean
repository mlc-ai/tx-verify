-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllScoreLoadWords
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedScoreTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Thread.Scores

noncomputable section

/-- Both repeated paths preserve the finite physical QK words through packing.
The lane can be suspended after the observed packs, and padding is admitted. -/
theorem repeatedPackedScoreShapeInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (mode : Repeated) (stage : Fin 2) {g start : Nat} {t : TState} {ending : Option TState}
    (ht : At t (scorePc mode.round 0) [])
    (hAddr : ∀ q : Fin 4, t.regs (scoreReg mode.round q) =
      some (b32 (scoreAddress l g stage q)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop start) ending)
    (hPresent : ending = none ∨ start+repeatedScoreStride mode*4 < (X.tr g).length) :
    ∃ (u : TState) (dot : Fin 4 → Fin 32 → ℝ), At u (scorePc mode.round 0+68) [] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+repeatedScoreStride mode*4)) ending ∧
      TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop start).take (repeatedScoreStride mode*4)) u ∧
      (∀ r, (∀ q : Fin 4,
          (r < repeatedScoreWordBase mode q ∨ repeatedScoreWordBase mode q+32 ≤ r) ∧
          ∀ k : Fin 16, r ≠ repeatedScorePairReg mode q k.val) → u.regs r = t.regs r) ∧
      ∀ (q : Fin 4) (k : Fin 16),
        let lo : Fin 32 := ⟨2*k.val,by have := k.isLt; omega⟩
        let hi : Fin 32 := ⟨2*k.val+1,by have := k.isLt; omega⟩
        u.regs (repeatedScorePairReg mode q k.val) =
          some (.pair (.float .f32 (dot q lo)) (.float .f32 (dot q hi))) := by
  have hFinite (q : Fin 4) (xs : List Value)
      (hLoad : X.get (g,start+repeatedScoreStride mode*q.val) =
        some ⟨scorePc mode.round q,.tc (.ld (scoreAddress l g stage q) xs .s32x32b)⟩)
      (word : Fin 32) : ∃ r, xs[word.val]? = some (.float .f32 r) := by
    obtain ⟨_,_,_,_,_,_,hWords⟩ := scoreLoadWordsOfLaunch hp hX hFrame mode.round q hLoad
    exact ⟨_,hWords word⟩
  have hBytes (q : Fin 4) (xs : List Value) (_ : (0 : Fin 4) ≤ q)
      (hLoad : X.get (g,start+repeatedScoreStride mode*q.val) =
        some ⟨scorePc mode.round q,.tc (.ld (scoreAddress l g stage q) xs .s32x32b)⟩) :
      ∀ k < 32, (xs.getD k (b32 0)).bytes = 4 := by
    intro k hk
    obtain ⟨_,hWord⟩ := hFinite q xs hLoad ⟨k,hk⟩
    simp [List.getD_eq_getElem?_getD,hWord,Value.bytes,FloatFmt.bytes]
  have hStart : Run kernel Assumptions.all l g t
      ((X.tr g).drop (start+repeatedScoreStride mode*(0 : Fin 4).val)) ending := by
    simpa only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] using hRun
  obtain ⟨u,hu,hWords,_,hKeep,hTail,hReach⟩ :=
    repeatedScoreTraceFromInPrefix hp mode stage 0 ht (fun q _ => hAddr q) hBytes hStart hPresent
  have hSource (q : Fin 4) := hWords q (Fin.zero_le _)
  choose words _ hLoads hPacks using hSource
  have hFinite' (q : Fin 4) (w : Fin 32) :
      ∃ r, (words q)[w.val]? = some (.float .f32 r) := hFinite q _ (hLoads q) w
  choose dot hDot using hFinite'
  refine ⟨u,dot,hu,hTail,?_,fun r h => hKeep r (fun q _ => h q),?_⟩
  · simpa only [Fin.val_zero,Nat.mul_zero,Nat.add_zero,Nat.sub_zero] using hReach
  · intro q k
    have hPair := hPacks q k.val k.isLt
    have hLo : (words q)[2*k.val]? = some (.float .f32 (dot q ⟨2*k.val,by omega⟩)) :=
      hDot q ⟨2*k.val,by omega⟩
    have hHi : (words q)[2*k.val+1]? = some (.float .f32 (dot q ⟨2*k.val+1,by omega⟩)) :=
      hDot q ⟨2*k.val+1,by omega⟩
    simpa only [List.getD_eq_getElem?_getD,hLo,hHi,Option.getD_some,joinValue] using hPair

end
end PTX.Kernels.TmlFa4Fwd.Softmax
