-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ev

@[expose] public section

/-! # The query loads of the MMA lane are at MMA pcs and fill with zero

A tensor load of a warp-4 lane is at a pc of the MMA code (`mma_qLoad_at`), and its descriptor is
the query map's: it fills with zero and its element is not `f64` (`mma_qLoad_zero`, from
`Pre.mapQBind`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hw : warp L y = 4)
include hp hX hFw hw

/-- **A tensor load of the MMA warp is at a pc of the MMA code.** -/
theorem mma_qLoad_at {i pc al : Nat} {s : TensorCopy.Spec}
    (he : X.get (y, i) = some ⟨pc, .tensorIssue al s⟩) : MmaAt L y pc := by
  have := lane4_inRole hp hX hFw hw he (.inr (.inr (.inl ⟨al, s, rfl⟩)))
  simp only [Mma.inRole, decide_eq_true_eq] at this
  exact ⟨hw, by omega, by omega⟩

/-- **A query load fills with zero** and its element is not `f64`. -/
theorem mma_qLoad_zero {i pc al : Nat} {s : TensorCopy.Spec}
    (he : X.get (y, i) = some ⟨pc, .tensorIssue al s⟩) :
    s.descriptor.fill = .zero ∧ s.descriptor.format ≠ .f64 := by
  obtain ⟨hr1, hr2⟩ := mma_qLoad_at hp hX hFw hw he |>.2
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) ⟨hr1, hr2⟩
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp only [Mma.EvK] at hE
  case qLoad i =>
    rcases hE with ⟨a', s', hk', -, -, -, ⟨-, -, hf, -⟩, ⟨bb, hb, hmap⟩, -, -⟩ | ⟨f, hf⟩
    · cases hk'
      rw [hp.param1Object] at hb
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      rw [hp.mapQBind] at hmap
      have hq := Option.some.inj hmap
      have h1 := congrArg (fun y : (n : Nat) × TensorDescriptor.Descriptor n => y.2.fill) hq
      refine ⟨h1.symm.trans (by simp [mapQ, encodeTiled]), fun h => ?_⟩
      rw [h] at hf
      simp [TensorDescriptor.Format.bytes] at hf
    · cases hf
  case leave i => exact absurd rfl (hl i)
  all_goals simp [Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
