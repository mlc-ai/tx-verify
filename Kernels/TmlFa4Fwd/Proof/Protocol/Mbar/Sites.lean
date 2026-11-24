-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MbarSite
public import Kernels.TmlFa4Fwd.Proof.Lib.Obj
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.MbarSite
public import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start

@[expose] public section

/-! # The mbarrier uses of each role's sites

Per role, the sites that name an mbarrier object, with the offset and the event's kind, read off the
shape tables: `epi_site`, `ld_use`, `mma_use`, `soft_mbar`, `corr_mbar2`. Every statement about who
uses a barrier is read off these (`Protocol/Mbar/SiteUse.lean`, `Protocol/Mbar/Use.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- An output-warp shape at a site that is no ready poll and no free arrival names no barrier. -/
macro "epi_none" : tactic => `(tactic| (
  rcases epi_site ‹_› ‹_› with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;>
    simp_all [Mma.Site.toE, Loader.Site.toE, Softmax.Site.toE, Correction.Site.toE]))

end
end PTX.Kernels.TmlFa4Fwd.Proof
