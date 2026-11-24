-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSignals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

def firstPublication : Round → Fin 8
  | .first => 1
  | .biased => 4
  | .unbiased => 6

def firstPublicationFacts (l : Launch) (stage : Fin 2) (round : Round) : List (Nat × Value) :=
  match round with
  | .biased => [(637, .pred (stage.val = 1)), (2535, b32 l.sharedBase)]
  | _ => [((signalSite (firstPublication round)).base, b32 (l.sharedBase + 8 * stage.val))]

def firstPublicationSteps (round : Round) : Nat :=
  if round = .biased then 4 else 1

/-- Prepare the stage base and count of the first P arrival from its actual local setup. -/
theorem firstPublicationSetup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (round : Round) (stage : Fin 2) :
    let s := signalSite (firstPublication round)
    Seg kernel Assumptions.all l g (firstPublicationSteps round) (probabilityWaitPc round false + 1)
      (firstPublicationFacts l stage round) s.pc
      [(s.base, b32 (l.sharedBase + 8 * stage.val)), (s.count, b32 1)] := by
  have hShared := hp.shared.2.1
  have hBase : l.sharedBase < 2 ^ 32 := by omega
  have hBase8 : l.sharedBase + 8 < 2 ^ 32 := by omega
  dsimp only
  cases round
  · intro t ht
    simp only [firstPublicationFacts, firstPublication, probabilityWaitPc, firstPublicationSteps,
      signalSite] at ht ⊢
    seg_fp ht using (simp [b32]; decide)
  · fin_cases stage <;> intro t ht <;>
      simp only [firstPublicationFacts, firstPublication, probabilityWaitPc, firstPublicationSteps,
        signalSite] at ht ⊢ <;>
      seg_fp ht using
        first
        | (change Value.bits 32
            (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) + 0#64)) =
              Value.bits 32 (BitVec.ofNat 64 l.sharedBase)
           rw [BitVec.add_zero, truncBits_ofNat hBase (by decide),
             truncBits_ofNat hBase (by decide)])
        | (change Value.bits 32
            (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) + BitVec.ofNat 64 8)) =
              Value.bits 32 (BitVec.ofNat 64 (l.sharedBase + 8))
           rw [truncBits_ofNat hBase (by decide), ← BitVec.ofNat_add,
             truncBits_ofNat hBase8 (by decide)])
        | decide
  · intro t ht
    simp only [firstPublicationFacts, firstPublication, probabilityWaitPc, firstPublicationSteps,
      signalSite] at ht ⊢
    seg_fp ht using (simp [b32]; decide)

end
end PTX.Kernels.TmlFa4Fwd.Softmax
