-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Proof.LoaderRingTail
public import Lemmas.Protocol.RingIndex
import Kernels.TmlFa4Fwd.Flow.Code.Part036
import Kernels.TmlFa4Fwd.Flow.Code.Part039

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Loader Epilogue
open MbarRing.Index

noncomputable section

/-- The physical slot of a logical use of the three-entry K/V ring. -/
def readyStage (use : Nat) : Fin 3 := ⟨slot 3 use, Nat.mod_lt _ (by decide)⟩

/-- The parity requested by that use, alternating only when the ring wraps. -/
def readyParity (use : Nat) : Bool := decide (round 3 use % 2 = 1)

theorem readyStage_succ (use : Nat) :
    (readyStage (use + 1)).val = ((readyStage use).val + 1) % 3 := by
  simp only [readyStage, slot]
  omega

theorem readyParity_succ (use : Nat) :
    readyParity (use + 1) = loaderNextPhase (readyStage use) (readyParity use) := by
  change decide (((use + 1) / 3) % 2 = 1) =
    xor (decide (use / 3 % 2 = 1)) (use % 3 == 2)
  by_cases hWrap : use % 3 = 2
  · have hRound : (use + 1) / 3 = use / 3 + 1 := by omega
    rw [hRound, hWrap]
    have hParity : (use / 3 + 1) % 2 = 1 ↔ ¬ use / 3 % 2 = 1 := by omega
    simp only [hParity, beq_self_eq_true]
    cases h : decide (use / 3 % 2 = 1)
    · have hn := of_decide_eq_false h
      simp [hn]
    · have hy := of_decide_eq_true h
      simp [hy]
  · have hRound : (use + 1) / 3 = use / 3 := by omega
    rw [hRound]
    simp [beq_eq_false_iff_ne.mpr hWrap]

/-- Which live register pair the decoded cursor uses for the first or second advance
in one MMA loop body. -/
def readyAdvanceSite : Fin 2 → Nat × (Nat × Nat) × (Nat × Nat)
  | 0 => (2344, (7207, 7208), (1192, 2572))
  | 1 => (2524, (1192, 2572), (7207, 7208))

end
end PTX.Kernels.TmlFa4Fwd.Mma
