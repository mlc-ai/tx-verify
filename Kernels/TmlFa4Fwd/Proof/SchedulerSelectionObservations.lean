-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.WarpScan
public import Lemmas.Kernel.ReadValue
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionReads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A full-warp scheduler ballot has exactly the bits of the lanes preceding the selected
batch within the group. The loop body and drain use the same mask and predicates. -/
theorem selectedGroupMask {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {g i ordinal pc first batch : Nat} {hit : Bool}
    {word : BitVec 32} (hFirst : first ≤ batch)
    (he : X.get (g, i) = some ⟨pc, .vote (2 ^ 32 - 1) hit word⟩)
    (hOrdinal : X.MaskK voteClass (g, i) (2 ^ 32 - 1) ordinal)
    (hPeers : ∀ lane < 32, ∃ j val,
      let e := (g - laneOf l g + lane, j)
      X.get e = some ⟨pc, .vote (2 ^ 32 - 1) (decide (first + lane < batch)) val⟩ ∧
        X.MaskK voteClass e (2 ^ 32 - 1) ordinal) :
    word = BitVec.ofNat 32 (2 ^ (batch - first) - 1) := by
  let part := fun lane => some (decide (first + lane < batch))
  have hInst : MaskInstance l voteClass X g (2 ^ 32 - 1) ordinal .ballot part := by
    intro lane hLane
    refine ⟨fun _ => .inl ?_, ?_⟩
    · obtain ⟨j, val, hv, hj⟩ := hPeers lane hLane
      exact ⟨j, pc, .vote (2 ^ 32 - 1) (decide (first + lane < batch)) val,
        decide (first + lane < batch), hv, rfl, hj, rfl⟩
    · intro h
      rw [Nat.testBit_two_pow_sub_one] at h
      simp [hLane] at h
  apply BitVec.eq_of_getLsbD_eq
  intro lane hLane
  have hBit := (hX.vote g i ordinal pc (2 ^ 32 - 1) hit word he hOrdinal
    part hInst lane hLane).1 _ rfl
  have heq : first + lane < batch ↔ lane < batch - first := by omega
  simpa only [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, decide_eq_true_eq,
    hLane, decide_true, Bool.true_and, ← heq] using hBit

/-- Indexed shuffles for batch selection use the verified source lane in the same instance. -/
theorem selectedIndexValue {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {g i j ordinal pc sourcePc lane : Nat}
    {src source recv peerRecv : Value} {ok peerOk : Bool} {peerIndex : Nat} (hLane : lane < 32)
    (he : X.get (g, i) = some ⟨pc, .shfl .idx src lane 31 recv ok⟩)
    (hk : X.ShflK (g, i) ordinal)
    (hp : X.get (g - laneOf l g + lane, j) =
      some ⟨sourcePc, .shfl .idx source peerIndex 31 peerRecv peerOk⟩)
    (hj : X.ShflK (g - laneOf l g + lane, j) ordinal)
    (hx : ¬ ShflExited X (g - laneOf l g + lane) ordinal) :
    recv = source ∧ ok = true := by
  have hSource := shflSource_idx (laneOf l g) hLane
  have hr := shfl_source_value hX he hk (by simpa only [hSource] using hp)
    (by simpa only [hSource] using hj) (by simpa only [hSource] using hx)
  simpa only [hSource] using hr

variable {p : Params} {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel A m X) {g i j ordinal first batch peerIndex : Nat} {t : TState}
    {F : List (Nat × Value)} {recv peerRecv : Value} {ok peerOk : Bool}
include hp hX

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
