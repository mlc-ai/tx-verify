-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasArrivalRank
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreNumericsProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption Correction Thread

/-- The actual returned Bias acquire and the decoded operands it carries into
the vector window, at one stage's named synchronization generation. -/
structure RepeatedBiasAcquireLane (l : Launch) (X : Execution) (g : Nat)
    (stage : Fin 2) (generation : Nat) (F : List (Nat × Value)) where
  warp : Fin 8
  stageEq : stageOf warp = stage
  cursor : OpeningTripCursor l X g 5184 F
  rank : observedBarrierOrdinal X (g,cursor.pos) (11+stage.val) = generation
  row : cursor.ready.regs 3976 = some (b32 (repeatedBiasRowBase l g))
  stageOffset : cursor.ready.regs 3977 = some (b32 (repeatedBiasStageOffset warp))
  vectorBase : ∀ j : Fin 14, cursor.ready.regs (3982+4*j.val) = some (b32 (kvSwizzle
    (repeatedBiasRowBase l g+repeatedBiasStageOffset warp+repeatedVectorDisplacement j)))
  addressKeeps : ∀ x ∈ F, x.1 ∉ [4166,4167,4168,4169,4170]
  vectorKeeps : ∀ x ∈ F, ∀ i, biasVectorKeeps true i x.1
  barrierKeeps : ∀ x ∈ F, x.1 ≠ biasBarReg true
  fenceFrame : ∀ x ∈ biasFenceFacts l g warp true, x ∈ F
  releaseKeeps : ∀ x ∈ F, x.1 ∉ biasReleaseWritten true

/-- The packed words retained by the Bias rendezvous are the finite operands
read by each decoded repeated FMA, in physical column order. -/
theorem PackedScorePrefix.biasedFmaInputsOfFootprint
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : OutputFootprint p X) {g : Nat} {stage : Fin 2}
    {F : List (Nat × Value)} {input : OpeningTripCursor l X g (scorePc .biased 0) F}
    (c : PackedScorePrefix l X g .biased stage 4 input) {s : TState}
    (hPacked : Holds s.regs (repeatedBiasPackFrame c.words)) :
    ∃ dot : Nat → ℝ, ∀ pair < 64,
      readERealPair l g s (.reg (7367+pair)) =
        some (.ok ((dot (2*pair) : EReal),(dot (2*pair+1) : EReal))) := by
  obtain ⟨dot,hDots⟩ := c.scoreColumnsOfFootprint hp hX hFootprint
  refine ⟨dot,?_⟩
  intro pair hPair
  let q : Fin 4 := ⟨pair/16,by omega⟩
  let k : Fin 16 := ⟨pair%16,by omega⟩
  have hWord : 16*q.val+k.val = pair := by dsimp [q,k]; omega
  have hReg : repeatedScorePairReg .biased q k.val = 7367+pair := by
    change 7367+16*q.val+k.val = 7367+pair
    omega
  have hRead : s.regs (repeatedScorePairReg .biased q k.val) =
      some (joinValue ((c.words q).getD (2*k.val) (b32 0))
        ((c.words q).getD (2*k.val+1) (b32 0))) := by
    apply holds_mem hPacked
    apply List.mem_flatMap.mpr
    exact ⟨q,by simp,List.mem_map.mpr ⟨k,by simp,rfl⟩⟩
  have hValues := repeatedPackedScoreValues (l := l) (g := g) .biased q k
    (fun w => dot (32*q.val+w.val)) (hDots q) hRead
  have hLow : 32*q.val+2*k.val = 2*pair := by omega
  have hHigh : 32*q.val+(2*k.val+1) = 2*pair+1 := by omega
  simpa only [hReg,hLow,hHigh] using hValues

end PTX.Kernels.TmlFa4Fwd.Softmax
