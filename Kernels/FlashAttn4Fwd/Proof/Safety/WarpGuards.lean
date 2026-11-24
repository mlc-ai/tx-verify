-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Assumptions
public import Kernels.FlashAttn4Fwd.Audit.AssumptionSites
public import Lemmas.Flow.PollLands

@[expose] public section

/-! # The kernel's poll guards

Every guarded `bra.uni` or aligned instruction of the kernel is the branch of a wait loop on the
poll right before it (the 37 `@P bra.uni` after a `try_wait`), decided on the code, and
`Assumptions.pollAgree` selects every such branch. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof

noncomputable section

set_option maxRecDepth 100000

/-- Every guarded `bra.uni` or aligned instruction is the branch of a wait loop on the poll
right before it, and every poll is followed by its branch. -/
theorem poll_guards : kernel.pollGuardsOk = true := by decide +kernel

/-- Every poll branch is a site of `Assumptions.pollAgree`: the sites are all the guarded
`bra.uni` positions (`Assumptions.pollAgreeSites_ops`). -/
theorem poll_selected : ∀ pc, kernel.pollBranch pc = true →
    Assumptions.all.any (·.uniPoll pc) = true := by
  intro pc hpc
  obtain ⟨-, -, dst, neg, tgt, base, off, par, acq, sc, hcb, -⟩ := pollBranch_spec hpc
  have hm : pc ∈ Assumptions.pollAgreeSites := by
    rw [Assumptions.pollAgreeSites_ops.2]
    exact List.mem_map.mpr ⟨(_, pc), List.mem_filter.mpr
      ⟨List.mem_zipIdx_iff_getElem?.mpr hcb, rfl⟩, rfl⟩
  rw [Assumptions.all_uniPoll]
  exact List.contains_iff_mem.mpr hm

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
