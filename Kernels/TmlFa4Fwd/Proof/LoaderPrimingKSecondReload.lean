-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute
public import Kernels.TmlFa4Fwd.Proof.LoaderPointerReload
public import Kernels.TmlFa4Fwd.Proof.LoaderScratchAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part009

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The initial K packet reloads the second saved pointer just before broadcasting its halves. -/
def primingKSecondReload : SavedPointerReload := ⟨609, 7292, 8, 1871, 1872⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
