-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaOperands

namespace PTX.Tests.TcMmaSafety
open TcMma
noncomputable section

private def L : Launch :=
  { grid := 2, block := 32, clusterSize := 2, params := fun _ => none }
private def smem : TcShared.Descriptor := ⟨0, 0, 1024, 0, false, false, .b128⟩
private def spec : OperandSpec :=
  ⟨⟨.two, .f16 .f16 .f32, 256, 256, false, false, false, false, false⟩, smem, smem, 0, 1, none, {}⟩

example : SharedEncoded smem := by
  unfold SharedEncoded smem
  decide
example : ¬ SharedEncoded { smem with start := 2^18 } := by
  intro h
  exact (Nat.lt_irrefl _) h.1

-- Canonical production addressing is defined for every byte, without enumeration.
example (op : Operand) (index : Nat)
    (hi : index < op.extent spec.descriptor * spec.descriptor.kind.k * spec.descriptor.kind.width) :
    ∃ loc, spec.byteLoc op index = some loc := by
  have bound : index / 32 < 256 := by
    cases op <;> simp [Operand.extent, spec, Kind.k, Kind.width] at hi <;> omega
  cases op <;>
    simp [OperandSpec.byteLoc, spec, Valid, Operand.extent, Operand.major, Kind.k, Kind.width,
      shapeOk, typesOk, transposeOk, TcShared.byteAddress, smem, bound,
      Nat.mod_lt _ (by decide : 0 < 2)]

-- Even a full mask may not excuse an out-of-range D allocation footprint.
example (mask : List Nat) : ¬ IssueShape L (0, 0) 300 spec mask := by
  intro h
  have hb := h.2.2.2.2.2.2.2.2.1
  change 300 + 256 ≤ 512 at hb
  omega

-- Pending work does not pretend to have already computed results.
example (X : Execution) (A : List Assumption) (i : EvId) (h : X.async.mmaDone i = false) :
    CompletedValues L A X i := by
  intro hd
  rw [h] at hd
  cases hd

-- Once complete, a nonempty output cannot bypass numerical interpretation.
example (X : Execution) (i : EvId) (cell : Cell) (hd : X.async.mmaDone i = true)
    (hc : X.MmaCell i cell)
    (hf : ∀ d s accum mask, X.MmaIssue i d s accum mask → s.descriptor.kind.width = 2) :
    ¬ CompletedValues L [] X i := by
  intro h
  obtain ⟨v, hv⟩ := h hd cell hc
  obtain ⟨d, s, accum, mask, sa, sb, sat, hi, hk⟩ := result_no_profile hv
  have := hf d s accum mask hi
  rw [hk] at this
  cases this

-- Exiting the peer while MMA is pending is rejected even if its operand reads finished: the
-- completion is the use of the operand CTA's shared memory (ERR-SHARED-LIFETIME).
example (K : Kernel) (A : List Assumption) (X : Execution) (i : EvId) (d : Nat) (s : OperandSpec)
    (accum : Bool) (mask : List Nat) (hi : X.MmaIssue i d s accum mask)
    (hx : CtaExited L X s.highCta) (hd : X.async.mmaDone i = false) :
    SharedLifetimeUnsafe L K A X := by
  refine ⟨.async i .mmaDone, s.highCta, ?_, .inr ⟨hx, fun h => ?_⟩⟩
  · refine .inr (.inr (.inr (.inr ⟨i, .mmaDone, rfl, ?_, ?_⟩)))
    · exact .inr (.inr (.inr (.inl ⟨.inl ⟨d, s, accum, mask, hi⟩, rfl⟩)))
    · exact .inl ⟨d, s, accum, mask, hi, .inr rfl⟩
  have done : X.async.mmaDone i = true := h.1
  rw [hd] at done
  cases done

end
end PTX.Tests.TcMmaSafety
