-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.HsLayer
public import Kernels.InklingRelDecode.Proof.Result.PrAll

@[expose] public section

/-!
# `Pr.MmaStates` for every consistent execution

The event at an MMA state at a QK step is a QK MMA of the iteration's block, at a PV step a PV
MMA of the previous block, with the counts of `Sr.QkAt` and `Sr.PvAt` (`Hs.qkAt_of`,
`Hs.pvAt_of`), for every handshake package whose committing lane is `Hs.cmOf` and whose base
column is `Hs.tmOf` (the package `Hs.pkg_of` is one).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Pr.MmaStates`.** -/
theorem mmaStates_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hb : BaseWordRead L X)
    (hn : NumWordRead Q L X) (hB : Mma.MmaBcast L X) (G : Sr.SrPkg L kernel asms mem0 X)
    (hcm : ∀ c, G.cm c = cmOf L X c) (htm : ∀ c, G.tm c = tmOf c) : Pr.MmaStates Q L G where
  qk := by
    intro g k j d P hg hk hσ hs
    rw [hcm, htm]
    exact qkAt_of hpre hX hf hR hb hn hB hg hk hσ hs
  pv := by
    intro g k j d P hg hk hσ hs
    rw [hcm, htm]
    exact pvAt_of hpre hX hf hR hb hn hB hg hk hσ hs

/-- **`Pr.MmaStates` of the package `pkg_of`.** -/
theorem mmaStates_pkg (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X)
    (hb : BaseWordRead L X) (hn : NumWordRead Q L X) (hI : ∀ i, Lk.ScratchIt Q L X i)
    (r : PkgRest L X) : Pr.MmaStates Q L (pkg_of hpre hX hf hR hb hn hI r) :=
  mmaStates_of hpre hX hf hR hb hn r.bcast _ (fun _ => rfl) (fun _ => rfl)

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
