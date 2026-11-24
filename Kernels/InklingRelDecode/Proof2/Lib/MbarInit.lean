-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.FirstPublished
public import Lemmas.Protocol.PairTmaRing.Hyp
public import Lemmas.Protocol.BarTable

@[expose] public section

/-!
# An mbarrier initialized once and published to its users

Moved from the first tree's `Protocol/MbarInit.lean` (names and namespace unchanged).

The generic step of `objectsPublished`, `mbarInit` and `SO.Facts.init` (the copy of FA4's
`InitFirst.initFirst_of_published`, with the lifetime facts the safety layer reads off it). An
object `m` with one initialization event `e` (count `c`), whose every other record is issued by an
event to which `e` is published (`InitPublished`: it happens before the issuer in base causality
order, or it is published through the init fence), in an execution with no invalidation:

* the initialization is the object's first record, without fault, and its only initialization
  (`initFirst_of_published`, the shape `SO.Facts.init` takes: `PairTmaRing.InitFirst`);
* every record lies in an initialized lifetime published to its issue (`objectPublished_of_init`,
  `Safety.Protocol.objectsPublished` for the barrier).

What is not here: that the initialization of each of the kernel's 12 barriers is published to the
issuer of every other record. That is the order of the prologue's initializations before the users
(`bar.sync 0, 128`, ordinal 2 of barrier 0, for the users inside the default partition; the first
generation of barrier 1 for the others), which is the named-barrier proof (the development notes,
"Protocol `Mbar`").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Mbar
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
end PTX.Kernels.InklingRelDecode.Proof.Mbar
