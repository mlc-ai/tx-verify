-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasReturn
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstFmaOperands
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreLoadWords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def openingBiasColumns (p : Params) (l : Launch) (g batch : Nat) (stage : Fin 2) :
    Nat → Option ℝ :=
  let coords := assignedCoordinates p batch (g/l.block)
  firstVisitBiasValue p batch (128*(2*coords.1+stage.val)+(g%l.block)%128) coords.2

/-- The first affine pass reaches the causal mask with its exact loaded QK and Bias values. -/
structure OpeningAffineLane (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) (stage : Fin 2) (wait : Nat) where
  entry : OpeningFmaLane p l X g batch stage wait
  dot : Nat → ℝ
  words : ∀ (q : Fin 4) (column : Fin 32), (entry.scores.words q)[column.val]? =
    some (.float .f32 (dot (32*q.val+column.val)))
  ready : TState
  reached : At ready 3850 []
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) entry.ready ready
  logits : firstMaskInputs ready (firstBiasLogit (abiFloat p.invScaleBits)
    (firstBiasRegisterValue (openingBiasColumns p l g batch stage)) (firstQkRegisterValue dot))
  frame : ∀ r ∉ [3088,3089,7895,7896,7897] ++ (biasBodyItems false).flatMap BiasAffineItem.writes,
    ready.regs r = entry.ready.regs r

/-- The actual finite QK words and selected Bias bytes justify all 64 affine pairs
in the first softmax visit on a consistent execution prefix. -/
theorem OpeningFmaLane.affineOfPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch wait : Nat} {stage : Fin 2}
    (entry : OpeningFmaLane p l X g batch stage wait)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    Nonempty (OpeningAffineLane p l X g batch stage wait) := by
  classical
  have hCuQ := (hFrame.metadataProtected hp).1
  have finiteWord (q : Fin 4) (k : Fin 32) : ∃ r,
      (entry.scores.words q)[k.val]? = some (.float .f32 r) :=
    scoreLoadFloatsOfOpeningResult hp hX hCuQ hFrame hb q hLo hHi
      (entry.scores.values.1 q).2 entry.scores.acquire k.val k.isLt
  choose point hPoint using finiteWord
  let dot (n : Nat) := point ⟨n/32%4,Nat.mod_lt _ (by decide)⟩ ⟨n%32,Nat.mod_lt _ (by decide)⟩
  have hDot (q : Fin 4) (k : Fin 32) :
      (entry.scores.words q)[k.val]? = some (.float .f32 (dot (32*q.val+k.val))) := by
    have hK := k.isLt
    have hQ := q.isLt
    have h1 : (32*q.val+k.val)/32%4 = q.val := by omega
    have h2 : (32*q.val+k.val)%32 = k.val := by omega
    have hFin1 : (⟨_,Nat.mod_lt _ (by decide)⟩ : Fin 4) = q := Fin.ext h1
    have hFin2 : (⟨_,Nat.mod_lt _ (by decide)⟩ : Fin 32) = k := Fin.ext h2
    simp only [dot,hFin1,hFin2,hPoint]
  let bias := openingBiasColumns p l g batch stage
  obtain ⟨hLow,hHigh,hFirst,hRest⟩ :=
    firstFmaOperandsOfWords entry.scores.values bias dot hDot entry.unpacked
  obtain ⟨_,inv,_,hInv,_,hPos⟩ := hp.scales
  have hBits : p.invScaleBits < 2^32 := (hp.values (14,p.invScaleBits)
    (by simp [Params.scalarWords])).1
  obtain ⟨u,hu,hRun,hLogit,hRegs⟩ := firstBiasScoreRun hPos hBits hInv
    (firstBiasRegisterValue bias) (firstQkRegisterValue dot)
    (entry.checkpoint.mono trivial) hLow hHigh entry.checkpoint.2.2.2.2.1 hFirst hRest
  have hAbi : abiFloat p.invScaleBits = (inv : ℝ) := by simp [abiFloat,hInv]
  refine ⟨⟨entry,dot,hDot,u,hu,run_rtg hRun,?_,hRegs⟩⟩
  rw [hAbi]
  exact hLogit

end
end PTX.Kernels.TmlFa4Fwd.Softmax
