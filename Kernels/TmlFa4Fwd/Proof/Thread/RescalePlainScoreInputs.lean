-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescalePackedInput
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedPackedScoreShape
import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainMaximum

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) (stage : Fin 2)
    {g start : Nat} {t : TState} {ending : Option TState} {a : Acc} {data : List Byte}
    (old : Option ℝ) (ht : At t (scorePc .unbiased 0) [])
    (hAddr : ∀ q : Fin 4, t.regs (scoreReg .unbiased q) = some (b32 (scoreAddress l g stage q)))
    (hOld : t.regs 7255 = some (scoreValue old)) (hScale : t.regs 7133 = some (b32 p.scaleLog2Bits))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop start) ending)
    (he : StatisticsStore X (g,start+8) (rescaleStore false) a data)
include hp hX hFrame stage old ht hAddr hOld hScale hr he

/-- The actual plain score loads supply all current maximum inputs.  This needs only
the running reference and ABI scale at the first load, including in a padded lane. -/
theorem rescalePlainArithmeticEntryOfLoadsWithPath :
    ∃ scores : Nat → Option ℝ, RescaleArithmeticEntryWith p l X (g,start+8) false
      (fun u =>
        TraceReach kernel Assumptions.all l g t (((X.tr g).drop start).take 8) u ∧
        (∀ (q : Fin 4) (k : Fin 16),
          u.regs (repeatedScorePairReg .unbiased q k.val) =
            some (.pair (scoreValue (scores (32*q.val+2*k.val)))
              (scoreValue (scores (32*q.val+(2*k.val+1)))))) ∧
        ∀ r, (∀ q : Fin 4,
          (r < repeatedScoreWordBase .unbiased q ∨ repeatedScoreWordBase .unbiased q+32 ≤ r) ∧
          ∀ k : Fin 16, r ≠ repeatedScorePairReg .unbiased q k.val) →
          r ∉ rescaleMaxWrites false → u.regs r = t.regs r) := by
  have hPresent : start+8 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨u,dot,hu,hTail,hPath,hKeep,hPairs⟩ :=
    repeatedPackedScoreShapeInPrefix hp hX hFrame .unbiased stage ht hAddr hr (.inr hPresent)
  let scores (col : Nat) : Option ℝ := some (dot
    ⟨col/32%4,Nat.mod_lt _ (by decide)⟩ ⟨col%32,Nat.mod_lt _ (by decide)⟩)
  have hPacked (q : Fin 4) (k : Fin 16) :
      u.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (scores (32*q.val+2*k.val)))
          (scoreValue (scores (32*q.val+(2*k.val+1))))) := by
    have hQ := q.isLt
    have hK := k.isLt
    have hIndex (x : Nat) (hx : x < 32) :
        (⟨(32*q.val+x)/32%4,Nat.mod_lt _ (by decide)⟩ : Fin 4) = q ∧
        (⟨(32*q.val+x)%32,Nat.mod_lt _ (by decide)⟩ : Fin 32) = ⟨x,hx⟩ := by
      constructor <;> apply Fin.ext <;> dsimp only
      · rw [show (32*q.val+x)/32 = q.val by omega, Nat.mod_eq_of_lt hQ]
      · omega
    obtain ⟨hl,hLo⟩ := hIndex (2*k.val) (by omega)
    obtain ⟨hh,hHi⟩ := hIndex (2*k.val+1) (by omega)
    simpa only [scores,hl,hLo,hh,hHi,scoreValue] using hPairs q k
  have hRead := plainMaximumInputs scores old hPacked
    ((hKeep 7255 (by decide)).trans hOld)
  have hEntry := rescaleArithmeticEntryOfPackedScoresWithFrame hp false
    (plainCombinedScores scores old) hu hRead ((hKeep 7133 (by decide)).trans hScale) hTail he
  refine ⟨scores,hEntry.mono (fun w hw => ⟨?_,?_,fun r hLoad hMax => ?_⟩)⟩
  · simpa only [List.append_nil, show repeatedScoreStride .unbiased * 4 = 8 from rfl] using
      hPath.append (TraceReach.of_local hw.1)
  · intro q k
    exact (hw.2 _ (by revert q k; decide +kernel)).trans (hPacked q k)
  · exact (hw.2 r hMax).trans (hKeep r hLoad)

theorem rescalePlainArithmeticEntryOfLoadsWithPairs :
    ∃ scores : Nat → Option ℝ, RescaleArithmeticEntryWith p l X (g,start+8) false
      (fun u =>
        (∀ (q : Fin 4) (k : Fin 16),
          u.regs (repeatedScorePairReg .unbiased q k.val) =
            some (.pair (scoreValue (scores (32*q.val+2*k.val)))
              (scoreValue (scores (32*q.val+(2*k.val+1)))))) ∧
        ∀ r, (∀ q : Fin 4,
          (r < repeatedScoreWordBase .unbiased q ∨ repeatedScoreWordBase .unbiased q+32 ≤ r) ∧
          ∀ k : Fin 16, r ≠ repeatedScorePairReg .unbiased q k.val) →
          r ∉ rescaleMaxWrites false → u.regs r = t.regs r) := by
  obtain ⟨scores,hEntry⟩ :=
    rescalePlainArithmeticEntryOfLoadsWithPath hp hX hFrame stage old ht hAddr hOld hScale hr he
  exact ⟨scores,hEntry.mono (fun _ h => h.2)⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
