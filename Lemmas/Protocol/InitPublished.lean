-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.BarTable
public import Lemmas.Protocol.PairTmaRing.Hyp
public import Lemmas.Kernel.Safety.Classes
public import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section

/-! # An mbarrier initialized once and published is initialized first

A proof tool, generic over the kernel. Two lemmas that the kernels with mbarriers each proved
for themselves (FlashAttn4Fwd, InklingRelDecode, TmlFa4Fwd), stated once:

* `ObjectInit.record_issuer`: the issuer of a record of an object's history is an event that
  names the object (`Frame.MbarOf`), and when that event is an initialization of the object the
  record is an initialization record. A kernel uses it to turn a fact about every *event* that
  names the object ("it follows the initialization") into a fact about every *record*.
* `ObjectInit.initFirst_of_published`: an object initialized by one event `e` only, whose
  initialization is published to the issuer of every other record (`InitPublished`: base
  causality, or the init fence with a cluster barrier), has a history that starts with that
  initialization, without fault (`PairTmaRing.InitFirst`, the premise of every ring
  structure of the library). -/

namespace PTX.ObjectInit

open AsyncCopy MBarrier

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **A record's issuer names its object**, and an issuer that is an initialization of it
issued an initialization record. -/
theorem record_issuer (hX : Consistent L K A mem0 X) {o : Loc} {r : Record Ref}
    (hr : r ∈ X.objects o) :
    ∃ ev, X.get r.id.issuer = some ev ∧ Frame.MbarOf ev o ∧
      ((∃ c, ev.kind = .mbInit o c) → ∃ n, r.action = .init n) := by
  cases record_source hX.tma.2.2.1 hr with
  | init hid he ha => rw [hid]; exact ⟨_, he, rfl, fun _ => ⟨_, ha⟩⟩
  | inval hid he ha => rw [hid]; exact ⟨_, he, rfl, fun ⟨_, h⟩ => by cases h⟩
  | arrive hid he ha => rw [hid]; exact ⟨_, he, rfl, fun ⟨_, h⟩ => by cases h⟩
  | wait hid he ha => rw [hid]; exact ⟨_, he, rfl, fun ⟨_, h⟩ => by cases h⟩
  | increment hid he ha => rw [hid]; exact ⟨_, he, rfl, fun ⟨_, h⟩ => by cases h⟩
  | tensor hid he hm ha => rw [hid]; exact ⟨_, he, hm, fun ⟨_, h⟩ => by cases h⟩
  | arriveOn hid he hm hn ha => rw [hid]; exact ⟨_, he, hm.symm, fun ⟨_, h⟩ => by cases h⟩
  | bulk hid he hc hn ha => rw [hid]; exact ⟨_, he, hc, fun ⟨_, h⟩ => by cases h⟩
  | commit hid he ht ha => rw [hid]; exact ⟨_, he, ⟨_, ht⟩, fun ⟨_, h⟩ => by cases h⟩
  | clc hid he hm htg ha => rw [hid]; exact ⟨_, he, ⟨_, htg, hm⟩, fun ⟨_, h⟩ => by cases h⟩

/-- **An object initialized once, published to its other records, is initialized first.** -/
theorem initFirst_of_published (hX : Consistent L K A mem0 X) {m : Loc} {e : EvId} {c : Nat}
    (hinit : X.MbInit e m c) (hcount : validCount c)
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

end PTX.ObjectInit
