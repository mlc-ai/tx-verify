-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.BarTable

@[expose] public section

/-! # An object initialized first is published to its records

ERR-OBJECT-LIFETIME (`ObjectPublished`) asks of every record of an mbarrier object that it lies in
the lifetime of an initialization: an initialization record needs nothing more (no invalidation
precedes it); any other record needs an initialization before it in the object's history, of the
same lifetime, published to its issuer (`InitPublished`), and before the invalidation that ends the
lifetime, if any.

For an object whose history starts with an initialization, without fault, in an execution
without invalidations, that is the publication of the initialization to the issuers of the other
records (`objectPublished_of_first`). The initialization record is fault-free
(`fault_of_first`). -/

namespace PTX
open AsyncCopy MBarrier

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **Every record of an object initialized first is published**, when the
initialization is published to the issuer of every other record and no event invalidates an
object. -/
theorem objectPublished_of_first (hX : Consistent L K A mem0 X) {m : Loc} {e : EvId} {c : Nat}
    {r0 : Record Ref} (h0 : (X.objects m)[0]? = some r0) (hid0 : r0.id = .thread e)
    (ha0 : r0.action = .init c) (hf0 : r0.fault = none) (hinit : X.MbInit e m c)
    (hinval : ∀ v m', ¬ X.MbInval v m')
    (hpub : ∀ s ∈ X.objects m, (∀ n, s.action ≠ .init n) → InitPublished L X e s.id.issuer m)
    {r : Record Ref} (hr : r ∈ X.objects m) : ObjectPublished L X m r := by
  by_cases hn : ∃ n, r.action = .init n
  · exact .inl ⟨hn, fun v hv => (hinval v m hv).elim⟩
  · have hnon : ∀ n, r.action ≠ .init n := fun n h => hn ⟨n, h⟩
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hr
    have hg : (X.objects m)[j]? = some r := by rw [← hget]; exact List.getElem?_eq_getElem hj
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · rw [hg] at h0
        cases h0
        exact (hnon c ha0).elim
      · exact h
    refine .inr ⟨e, c, hinit, ⟨0, j, r0, r, c, h0, hid0, ha0, hf0, hg, rfl, hj0, ?_⟩,
      hpub r hr hnon, fun v hv => (hinval v m hv).elim⟩
    exact (objects_noInval hX.tma.2.2.1 hinval m).sameLifetime 0 j

/-- The initialization records of an object initialized first, once, without fault, are
fault-free. -/
theorem fault_of_first {m : Loc} {r0 : Record Ref} (hf0 : r0.fault = none)
    (hone : ∀ q ∈ X.objects m, (∃ n, q.action = .init n) → q = r0) {r : Record Ref}
    (hr : r ∈ X.objects m) (hn : ∃ n, r.action = .init n) : r.fault = none := by
  rw [hone r hr hn]
  exact hf0

end

end PTX
