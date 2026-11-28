-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.FirstPublished
public import Lemmas.Protocol.PairTmaRing.Hyp
public import Lemmas.Protocol.BarTable

@[expose] public section

/-! Unique, published initialization of an mbarrier and its subsequent lifetime. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

variable (hX : Consistent L K A mem0 X) {m : Loc} {e : EvId} {c : Nat} (hinit : X.MbInit e m c)
    (hcount : validCount c) (hsite : ∀ i pc n, X.get i = some ⟨pc, .mbInit m n⟩ → i = e ∧ n = c)
include hX hinit hcount hsite

/-- **An object initialized once, published to its other records, is initialized first.** -/
theorem initFirst_of_published
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

/-- **Every record of an object initialized once and published lies in an initialized lifetime
published to its issue**, in an execution with no invalidation. -/
theorem objectPublished_of_init (hinval : ∀ v m', ¬ X.MbInval v m')
    (hpub : ∀ s ∈ X.objects m, (∀ n, s.action ≠ .init n) → InitPublished L X e s.id.issuer m) :
    ∀ r ∈ X.objects m, ObjectPublished L X m r := by
  intro r hr
  obtain ⟨r0, h0, hid, ha, hf, -⟩ := init_record_success_of_unique_init hX hinit hcount
    (fun _ s _ hs ha => (BarTable.init_source_of_site hX hsite (List.mem_of_getElem? hs) ha).1)
    (fun _ s hs hnon => object_not_before_of_published hX ⟨c, hinit⟩
      (hpub s (List.mem_of_getElem? hs) hnon))
  exact objectPublished_of_first hX h0 hid ha hf hinit hinval hpub hr

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
