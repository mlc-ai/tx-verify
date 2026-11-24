-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleBiasWords
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasVector
import Kernels.TmlFa4Fwd.Proof.SoftmaxLaterBiasVectorTrace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Thread Thread.Scores

noncomputable section

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) (stage : Fin 2)
    {g start : Nat} {t : TState} {ending : Option TState} (ht : At t (biasReadPc true 0) [])
    (hBases : ∀ i, t.regs (biasReadSite true i).base = some (b32 (biasVectorBase l g stage true i)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop start) ending)
include hp hX hFrame stage ht hBases hRun

/-- The actual repeated Bias vectors retain a canonical BF16 value for all 128
columns, including padding, before the fence. -/
theorem repeatedBiasUnpackShapePathGuarded {cursor : Nat → Prop} (hCursor : cursor start)
    (hAdvance : ∀ j site a bytes, X.get (g,j) = some ⟨site,.rd a bytes⟩ → cursor j → cursor (j+1))
    (hPresent : ∀ k, start ≤ k → k ≤ start+64 → cursor k → ending = none ∨ k < (X.tr g).length) :
    ∃ (u : TState) (bias : Nat → Option ℝ), At u (biasFencePc true) [] ∧
      (∀ i : Fin 16, BiasUnpacked true i u (fun k =>
        biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1)))) ∧
      (∀ r, (∀ i, biasVectorKeeps true i r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+64)) ending ∧ cursor (start+64) ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop start).take 64) u := by
  let base := fun i => biasVectorBase l g stage true i
  have hAddr (i : Fin 16) : base i + (biasReadSite true i).offset < 2^32 := by
    rw [show base i = biasVectorBase l g stage true i from rfl,biasVectorBase_add]
    exact (biasVectorAddressBounds hp g stage i).1
  have hAlign (i : Fin 16) : (base i + (biasReadSite true i).offset)%16 = 0 := by
    rw [show base i = biasVectorBase l g stage true i from rfl,biasVectorBase_add]
    exact (biasVectorAddressBounds hp g stage i).2
  let expected (i : Fin 16) (k : Nat) (bs : List (Option Byte)) :=
    X.get (g,start+4*i.val+k) = some ⟨biasReadPc true i,.rd (biasReadAcc l g (base i) true i k) bs⟩
  have hData (i : Fin 16) (k : Nat) : ∃ lo hi : Option ℝ, ∀ bs, expected i k bs →
      rebuild 3 bs = .ok (biasLoadWord lo hi) := by
    by_cases h : ∃ bs, expected i k bs
    · obtain ⟨bs,he⟩ := h
      obtain ⟨lo,hi,hWord⟩ := repeatedBiasWordShapeInPrefix hp hX hFrame
        (show BiasVectorRead X (g,start+4*i.val+k) true i
          (biasReadAcc l g (base i) true i k) bs from he)
      refine ⟨lo,hi,fun bytes hGet => ?_⟩
      have hBytes := (Kind.rd.inj (congrArg Event.kind (Option.some.inj (hGet.symm.trans he)))).2
      exact hBytes.symm ▸ hWord
    · exact ⟨none,none,fun bs hb => (h ⟨bs,hb⟩).elim⟩
  choose lo hi hData using hData
  let words := fun i k => biasLoadWord (lo i k) (hi i k)
  obtain ⟨u,hu,hRead,hKeep,hTail,hNext,hPath⟩ :=
    biasVectorsTraceWithPathGuarded true base words
      (fun i k _ => biasLoadWordShape (lo i k) (hi i k)) ht hBases hAddr hAlign
      hCursor (fun i k _ _ => hData i k)
      (fun i k _ bs h => hAdvance _ _ _ bs h) hRun hPresent
  let bias (col : Nat) : Option ℝ :=
    let vec : Fin 16 := ⟨col/8%16,Nat.mod_lt _ (by decide)⟩
    let word := col%8/2
    if col%2 = 0 then lo vec word else hi vec word
  refine ⟨u,bias,hu,?_,hKeep,hTail,hNext,hPath⟩
  intro i k hk
  have hi' := i.isLt
  have hIndex (b : Nat) (hb : b < 2) :
      (⟨(8*i.val+2*k+b)/8%16,Nat.mod_lt _ (by decide)⟩ : Fin 16) = i ∧
      (8*i.val+2*k+b)%8/2 = k ∧ (8*i.val+2*k+b)%2 = b := by
    constructor
    · apply Fin.ext
      dsimp only
      rw [show (8*i.val+2*k+b)/8 = i.val by omega, Nat.mod_eq_of_lt hi']
    · omega
  have hLow : bias (8*i.val+2*k) = lo i k := by
    obtain ⟨hI,hK,hB⟩ := hIndex 0 (by decide)
    simpa only [bias,Nat.add_zero] using
      (show bias (8*i.val+2*k+0) = lo i k by simp only [bias,hI,hK,hB,ite_true])
  have hHigh : bias (8*i.val+2*k+1) = hi i k := by
    obtain ⟨hI,hK,hB⟩ := hIndex 1 (by decide)
    simp only [bias,hI,hK,hB,Nat.one_ne_zero,ite_false]
  simpa only [hLow,hHigh,words] using (hRead i).2 k hk

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) (stage : Fin 2)
    {g start pos site : Nat} {a : Acc} {bytes : List Byte} {t : TState} {ending : Option TState}
    (ht : At t (biasReadPc true 0) [])
    (hBases : ∀ i, t.regs (biasReadSite true i).base = some (b32 (biasVectorBase l g stage true i)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop start) ending) (hBefore : start ≤ pos)
include hp hX hFrame stage ht hBases hRun hBefore

/-- A later write supplies the required span of all 64 Bias reads in its own prefix. -/
theorem repeatedBiasUnpackShapePathBeforeWrite (he : X.get (g,pos) = some ⟨site,.wr a bytes⟩) :
    ∃ (u : TState) (bias : Nat → Option ℝ), At u (biasFencePc true) [] ∧
      (∀ i : Fin 16, BiasUnpacked true i u (fun k =>
        biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1)))) ∧
      (∀ r, (∀ i, biasVectorKeeps true i r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start+64)) ending ∧ start+64 ≤ pos ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop start).take 64) u := by
  apply repeatedBiasUnpackShapePathGuarded hp hX hFrame stage ht hBases hRun
    (cursor := (· ≤ pos)) hBefore
  · intro j site a bytes hGet hBefore
    rcases Nat.eq_or_lt_of_le hBefore with rfl | hLater
    · have h := congrArg Event.kind (Option.some.inj (hGet.symm.trans he))
      cases h
    · omega
  · intro j _ _ hJ
    exact .inr (hJ.trans_lt (List.getElem?_eq_some_iff.mp he).1)

end
end PTX.Kernels.TmlFa4Fwd.Softmax
