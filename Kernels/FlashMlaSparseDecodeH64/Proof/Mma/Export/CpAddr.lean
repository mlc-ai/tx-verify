-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc

@[expose] public section

/-! # The source of the MMA lane's copy to column `256 + 8 k` is `keyDesc S k`

Copy `k` of the prologue copies to column `256 + 8 k` from the descriptor `keyDesc S k`
(`mma_cp_addr`): the copy to a given column has the source of the same index. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A copy of the lane to column `256 + 8 k` has the source of copy `k`.** -/
theorem mma_cp_addr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i pc : Nat} {c : TcCopy.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tc (.cp c)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) {k : Nat}
    (ha : c.address = 256 + 8 * k) :
    c.src = MmaFoot.keyDesc L.sharedBase k := by
  obtain ⟨d, hR, ⟨hpc, hE⟩, hl, hw⟩ := mma_at hp hX hFw hi (fun _ h => by cases h) hr
  have hg : g < L.threads := Frame.lt_of_get hX hi
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp only [Mma.EvK] at hE
  case qCopy k' =>
    rcases hE with ⟨s', hk', hsh, hfmt, haddr, hct, hsrc⟩ | ⟨f, hf⟩
    · cases hk'
      rw [Mma.cpW_decode hp k'.isLt] at hsrc
      have hkk : k = k'.val := by
        simp only [Mma.cpCol] at haddr
        omega
      rw [← hkk] at hsrc
      exact (Option.some.inj hsrc).symm
    · cases hf
  case leave k => exact absurd rfl (hl k)
  all_goals simp [Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
