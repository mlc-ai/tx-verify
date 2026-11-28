-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MmaSlot
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.SvCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ring
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.LagQk
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.PvStore
import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # A successful `qkDone` poll of warpgroup 0 observes the commit of its block

A warpgroup-0 lane that polled `qkDone (r % 2)` successfully for use `r / 2` (the load of block `r`:
`wg0_ldPlace`) has an MMA-lane commit to that slot, the `r / 2`-th, before which the lane issued
`24 r + 16` MMAs (`mma_qkCommit`): the commit of block `r`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

namespace TmRace

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **The commit of block `r`**: a lane `h` of warpgroup 0 with `r / 2 + 1` successful polls of
`qkDone (r % 2)` before an event `k` has a commit of the MMA lane to that slot with `r / 2`
earlier commits, `24 r + 16` MMA issues before it, and a QK MMA 15 of the block before it. -/
theorem qk_commit_poll {h k r : Nat}
    (hat : MbarRow.warp L h < 4)
    (hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (h / L.block) (.qkDone (slot2 r))) ((X.tr h).take k)) :
    ∃ ic pcc sp, X.get (mmaLane L X (h / L.block), ic) = some ⟨pcc, .tc (.commit sp)⟩ ∧
      sp.mbar = mbarLoc L (h / L.block) (.qkDone (slot2 r)) ∧
      ((X.tr (mmaLane L X (h / L.block))).take ic).countP
        (PTX.Flow.commitsTo (mbarLoc L (h / L.block) (.qkDone (slot2 r)))) = r / 2 ∧
      r < blocksOf P L (h / L.block) ∧
      mmaIssues ((X.tr (mmaLane L X (h / L.block))).take ic) = 24 * r + 16 ∧
      ∃ x < ic, ∃ pcx sx acc mask, X.get (mmaLane L X (h / L.block), x) =
        some ⟨pcx, .tc (.mma 400 sx acc mask)⟩ ∧ MbarRow.MmaAt L (mmaLane L X (h / L.block)) pcx ∧
        mmaIssues ((X.tr (mmaLane L X (h / L.block))).take x) = 24 * r + 15 := by
  obtain ⟨b', hbq⟩ := wg0_lane hp (pc := 103) ⟨hat, by omega, by omega⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = h / L.block := ⟨_, rfl⟩
  rw [← hcd] at hbq hpol ⊢
  obtain ⟨j, pcp, p, acq, sc, hjk, hget, hq⟩ := UnitHandoff.exists_poll hpol
  have O := qkDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c (slot2 r)
  rw [hbq] at hget hq
  obtain ⟨ic, pcc, sp, rank, hcom, hmb, htg, hcnt, hrank, hobs⟩ :=
    O.observes hX (u := r / 2) (qkReach hp hX hFw hR hI hB c (slot2 r) b') hget hq
  rw [← hbq] at hget hobs
  obtain ⟨rfl, rfl⟩ := mbarWait_cta hX hR hget
  obtain ⟨-, r', hr', hs, hall, hn, x, hxi, hM⟩ := mma_qkCommit hp hX hFw hcom hmb
  simp only [slot2, Fin.mk.injEq] at hs
  have hrr : r' = r := by omega
  subst hrr
  exact ⟨ic, pcc, sp, hcom, hmb, hcnt, hr', hn, x, hxi, hM⟩

end
end TmRace
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
