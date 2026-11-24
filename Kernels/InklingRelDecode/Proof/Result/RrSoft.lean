-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.RdSLoad

@[expose] public section

/-!
# The softmax threads of the package are the default-partition threads (`Rd.SoftAll`)

The package's softmax threads of a CTA are `Sr.SoftOf`: the launched threads of the CTA whose
index in the block is below 128 (the warps 0 to 3). `Mbar.Route.soft_thread` already needs the
inclusion in that set; the other inclusion is the definition, so a package cannot choose a
smaller set. `Rd.SoftAll` is then the definition's unfolding.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rd
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof

noncomputable section

/-- **`Rd.SoftAll`**: every default-partition thread of a CTA is a softmax thread of the
package. -/
theorem softAll {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (G : Sr.SrPkg L K A mem0 X) : SoftAll L G :=
  fun _ _ _ hg hgc hlt => ⟨hg, hgc, hlt⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Rd
