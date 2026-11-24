-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Classes
public import Lemmas.Protocol.FirstPublished
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PairTmaRing.Hyp

@[expose] public section

/-! # mbarrier object lifetime from initialization first

A proof skeleton, generic over the kernel, for ERR-OBJECT-LIFETIME (`TmaUnsafe`) in a kernel
that never invalidates an mbarrier and initializes each object before any other operation on it
(the startup's initializations). Each part of the check:

* **Lifetimes** (`ObjectPublished`): an object whose history starts with its one fault-free
  initialization (`PairTmaRing.InitFirst`) has every record in that lifetime when the
  initialization is published to the issue of every other record (`objectPublished_of_first`).
  The publication is the kernel's hand-off (as for ERR-MBAR-UNINITIALIZED,
  `Safety/Init.lean`).
* **Record faults**: the initialization record's is `InitFirst`'s; the other records' are the
  kernel's protocol facts (rings, unit hand-offs: `hfault`).
* **Accesses of an object's bytes**: none, when no footprint an access names meets an object
  (`hacc`); on a role table, from the access frame (`RoleTable.intent_at`) and the object frame
  (`RoleTable.mbar_frame`): `RoleTable.noObjectAccess`.
* **`cp.async` groups and masked bulk copies**: the kernel's (`hov`, `hmask`); for a kernel
  without linear copies, `noTmaUnsafe_of_noCopy`.

`noTmaUnsafe_of_first` assembles them. -/

namespace PTX.Frame

open PTX PTX.Flow AsyncCopy

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **ERR-OBJECT-LIFETIME from initialization first**: no invalidation; every object with a
record is initialized first, once and without fault; the initialization is published to the
issue of every other record of the object, whose records are fault-free; no access meets an
object's bytes; no `cp.async` group overlap and no unallocated masked range. -/
theorem noTmaUnsafe_of_first (hX : Consistent L K A mem0 X)
    (hinval : ∀ v m, ¬ X.MbInval v m)
    (hfirst : ∀ m, (X.objects m) ≠ [] → ∃ c, PairTmaRing.InitFirst X m c)
    (hpub : ∀ m e c, X.MbInit e m c → ∀ s ∈ X.objects m, (∀ n, s.action ≠ .init n) →
      InitPublished L X e s.id.issuer m)
    (hfault : ∀ m r, r ∈ X.objects m → (∀ n, r.action ≠ .init n) → r.fault = none)
    (hacc : ∀ e a w i m c l, X.Intent e a w → X.MbInit i m c → a.Covers l →
      ¬ Acc.Covers { loc := m, size := 8 } l)
    (hov : ¬ CpAsyncOverlap X) (hmask : ¬ MaskedRangeUnalloc mem0 X) :
    ¬ TmaUnsafe L mem0 X := by
  have hfirst' : ∀ m r, r ∈ X.objects m → ∃ c r0, (X.objects m)[0]? = some r0 ∧
      r0.action = .init c ∧ r0.fault = none ∧
      ∀ q ∈ X.objects m, (∃ n, q.action = .init n) → q = r0 := by
    intro m r hr
    obtain ⟨c, hc⟩ := hfirst m (List.ne_nil_of_mem hr)
    obtain ⟨r0, h0, ha0, hf0, hone⟩ := hc r hr
    exact ⟨c, r0, h0, ha0, hf0, hone⟩
  rintro (⟨m, r, hrm, hf⟩ | ⟨m, r, hrm, hp⟩ | ⟨e, a, w, i, m, c, l, hint, hi, hla, hlm, -⟩ | h | h)
  · obtain ⟨c, r0, -, -, hf0, hone⟩ := hfirst' m r hrm
    by_cases hn : ∃ n, r.action = .init n
    · rw [fault_of_first hf0 hone hrm hn] at hf; exact absurd hf (by simp)
    · rw [hfault m r hrm fun n h => hn ⟨n, h⟩] at hf; exact absurd hf (by simp)
  · obtain ⟨c, r0, h0, ha0, hf0, -⟩ := hfirst' m r hrm
    cases record_source hX.tma.2.2.1 (List.mem_of_getElem? h0) with
    | @init g j pc c' hid he ha' =>
      rw [ha0] at ha'
      cases ha'
      exact hp (objectPublished_of_first hX h0 hid ha0 hf0 ⟨pc, he⟩ hinval
        (fun s hs hnon => hpub m (g, j) c ⟨pc, he⟩ s hs hnon) hrm)
    | inval _ _ ha' | arrive _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | commit _ _ _ ha'
    | clc _ _ _ _ ha' | increment _ _ ha' | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' =>
      rw [ha0] at ha'; cases ha'
  · exact hacc e a w i m c l hint hi hla hlm
  · exact hov h
  · exact hmask h

/-- **ERR-OBJECT-LIFETIME for a kernel without linear copies.** -/
theorem noTmaUnsafe_of_noCopy (hX : Consistent L K A mem0 X)
    (hinval : ∀ v m, ¬ X.MbInval v m)
    (hfirst : ∀ m, (X.objects m) ≠ [] → ∃ c, PairTmaRing.InitFirst X m c)
    (hpub : ∀ m e c, X.MbInit e m c → ∀ s ∈ X.objects m, (∀ n, s.action ≠ .init n) →
      InitPublished L X e s.id.issuer m)
    (hfault : ∀ m r, r ∈ X.objects m → (∀ n, r.action ≠ .init n) → r.fault = none)
    (hacc : ∀ e a w i m c l, X.Intent e a w → X.MbInit i m c → a.Covers l →
      ¬ Acc.Covers { loc := m, size := 8 } l)
    (hcopy : ∀ i s, ¬ X.Copy i s) : ¬ TmaUnsafe L mem0 X :=
  noTmaUnsafe_of_first hX hinval hfirst hpub hfault hacc
    (not_cpAsyncOverlap_of_none fun i s h _ => hcopy i s h)
    (not_maskedRangeUnalloc_of_none fun i s _ h _ => hcopy i s h)

variable {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop}

/-- **No access meets an object's bytes, from the frames of a role table**: every access issued
by a thread of `S` names footprints (`AccessOf`, `AsyncOf`) outside every object of the object
frame `O`, every initialization of a thread of `S` names an object of its frame, and the threads
outside `S` neither access nor initialize (`hall`). -/
theorem RoleTable.noObjectAccess (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S) (hF : T.Followed X S)
    (hall : ∀ g < L.threads, S g) {O : Nat → Loc → Prop}
    (hO : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ m, MbarOf e m → O g m)
    (hA : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ a, (AccessOf e a ∨ AsyncOf e a) →
      ∀ l, a.Covers l → ∀ g' m, O g' m → ¬ Acc.Covers { loc := m, size := 8 } l) :
    ∀ e a w i m c l, X.Intent e a w → X.MbInit i m c → a.Covers l →
      ¬ Acc.Covers { loc := m, size := 8 } l := by
  intro e a w i m c l hint hi hl
  obtain ⟨pc, hie⟩ := hi
  have hgi := hall _ (lt_of_get hX hie)
  have hOm : O i.1 m := RoleTable.mbar_frame hC hX hT hF hO (.inr (.inr (.inr (.inr (.inr
    (.inr (.inr (.inr ⟨c, pc, hie⟩)))))))) hgi
  obtain ⟨ev, hev, hae⟩ := intent_issuer hint
  have hub : ∀ f, ev.kind ≠ .ub f := by
    obtain ⟨pc', k⟩ := ev
    rintro f rfl
    rcases hae with h | h <;> simp only [AccessOf, AsyncOf] at h
  have hge := hall _ (lt_of_get hX hev)
  obtain ⟨d, -, hJ, hinv, hEv⟩ := RoleTable.ev_of_ne_ub hC hX hT hF hge hev hub
  exact hA _ hge d ev hJ hinv hEv a hae l hl i.1 m hOm

end

end PTX.Frame
