-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Hyp
import Lemmas.Protocol.BarTable

@[expose] public section

/-! # An object initialized once and published is initialized first (library candidate)

`initFirst_of_published`: an object whose every initialization is one event `e` with one valid
count, published to the issuer of every other record, has `e`'s fault-free initialization as its
first record and no other (`PairTmaRing.InitFirst`). The same proof as FA4's
`Proof/Protocol/InitFirst.lean`, generic over the kernel (a lane-L candidate). -/

namespace PTX
open AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **An object initialized once, published to its other records, is initialized first.** -/
theorem initFirst_of_published (hX : Consistent L K A mem0 X) {m : Loc} {e : EvId}
    {c : Nat} (hinit : X.MbInit e m c) (hcount : MBarrier.validCount c)
    (hsite : ∀ i pc n, X.get i = some ⟨pc, .mbInit m n⟩ → i = e ∧ n = c)
    (hpub : ∀ s ∈ X.objects m, (∀ n, s.action ≠ .init n) → InitPublished L X e s.id.issuer m) :
    PairTmaRing.InitFirst X m c := by
  intro _ _
  obtain ⟨r0, h0, hid, ha, hf, -⟩ := init_record_success_of_unique_init hX hinit hcount
    (fun _ s _ hs ha => (BarTable.init_source_of_site hX hsite (List.mem_of_getElem? hs) ha).1)
    (fun _ s hs hnon => object_not_before_of_published hX ⟨c, hinit⟩
      (hpub s (List.mem_of_getElem? hs) hnon))
  refine ⟨r0, h0, ha, hf, fun q hq ⟨n, hqa⟩ => ?_⟩
  exact hX.record_eq hq (List.mem_of_getElem? h0)
    ((BarTable.init_source_of_site hX hsite hq hqa).1.trans hid.symm)

end
end PTX
