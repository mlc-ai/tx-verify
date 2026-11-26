-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Obs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Wg0Poll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Dealloc
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Final
import Lemmas.Kernel.SharedLifetime

@[expose] public section

/-! # An MMA or copy finishes before its CTA exits

Warpgroup 0's lane 0 of the CTA exits, so it made its barrier-12 event (`wg0_exitBar12`) and,
before it, its poll of `svDone` at pc 1184 (`wg0_bar12_poll`), which observes the notification of
the MMA lane's last commit, and that commit tracks every MMA and copy of the lane
(`svDone_done`). The poll is a canonical spin that resumes the lane's exit. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX PTX.Flow PTX.AsyncCopy MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : BarRows P L X) (hMb : MbarRows P L X) (hI : InitRows L X)
  (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hMb hI hB hN

/-- **Every MMA and copy finishes before an exit of its CTA**, once the CTA exited. -/
theorem life_mma : MmaFinished L kernel Assumptions.all X := by
  intro i hi hx
  obtain ⟨y0, i0⟩ := i
  obtain ⟨pc0, k0, hx0, hk0⟩ : ∃ pc0 k0, X.get (y0, i0) = some ⟨pc0, .tc k0⟩ ∧
      ((∃ b sp acc mask, k0 = .mma b sp acc mask) ∨ ∃ cs, k0 = .cp cs) := by
    rcases hi with ⟨b, sp, acc, mask, pc0, hx0⟩ | ⟨cs, pc0, hx0⟩
    · exact ⟨pc0, _, hx0, .inl ⟨b, sp, acc, mask, rfl⟩⟩
    · exact ⟨pc0, _, hx0, .inr ⟨cs, rfl⟩⟩
  obtain ⟨hatm, h1853⟩ := TmRace.mma_role hp hX hFw hx0 hk0
  have hgm : y0 = mmaLane L X (y0 / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx0 (fun _ h => by cases h) ⟨hatm, h1853⟩
  have hgm' : mmaLane L X (y0 / L.block) = y0 := hgm.symm
  have hy0 : y0 < L.threads := Frame.lt_of_get hX hx0
  obtain ⟨y, jw, p, hy, hyc, hy4, hpoll⟩ := exit_poll1184 hp hX hFw hR hy0 hx
  obtain ⟨hobs, -⟩ := svDone_done (pc0 := pc0) (i0 := i0) hp hX hFw hMb hI hB hN hy4
    (by rw [hgm']) hpoll (by rw [hgm']; exact hx0) (by rw [hgm']; exact hatm) h1853 hk0
  rw [hgm'] at hobs
  obtain ⟨finish, hOwn, hPath⟩ := exit_after_poll hX hpoll (by simpa only [hyc] using hx)
  obtain ⟨hd, hcb⟩ := CompletedBefore.of_observesMma (L := L) (K := kernel)
    (A := Assumptions.all) hX.tcCommit hobs hPath
  exact SharedFinished.of_completedBefore hd (by simpa only [hyc] using hOwn) hcb

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
