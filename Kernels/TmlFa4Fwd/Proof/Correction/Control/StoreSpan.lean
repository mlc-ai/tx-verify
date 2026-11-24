-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Span

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof

def afterStoreSite (st : Fin 2) (j : Fin 16) (h : Fin 2) : Site :=
  if h.val = 0 then .fst st j 1 else if j.val = 15 then .fence st else .fld st (j+1)

abbrev StoreSpan (p : Params) (L : Launch) (g : Nat) (v : V) (st : Fin 2) (j : Fin 16)
    (h : Fin 2) := SegU kernel Assumptions.all L g ((Site.fst st j h).pc+1)
      (facts p L g ⟨.fst st j h, v, 3⟩) (afterStoreSite st j h).pc
      (facts p L g ⟨afterStoreSite st j h, v, 0⟩)

theorem copy_span {s dst : Site} {p L g v k}
    (hsp : spanOk s dst = true) (hsub : (liveAt dst).all (liveAt s).contains = true)
    (hv : ∀ r ∈ liveAt dst, valueOf p L g ⟨s,v,k⟩ r = valueOf p L g ⟨dst,v,0⟩ r) :
    SegU kernel Assumptions.all L g (s.pc+1) (facts p L g ⟨s,v,k⟩) dst.pc
      (facts p L g ⟨dst,v,0⟩) := by
  intro t ht
  apply cross_span hsp _ t
  apply ht.mono
  apply holds_of_pointwise
  intro r hr
  rw [← hv r hr]
  obtain ⟨_, _, _, _, hregsAt⟩ := ht
  exact holds_mem hregsAt (mem_factsFrom
    (List.contains_iff_mem.mp (List.all_eq_true.mp hsub r hr)))

theorem store_span_copy {p L g v st j} (hj : 4 ≤ j.val) : StoreSpan p L g v st j 0 := by
  have table : ∀ (st : Fin 2) (j : Fin 16), 4 ≤ j.val →
      spanOk (.fst st j 0) (.fst st j 1) = true ∧
      (liveAt (.fst st j 1)).all (liveAt (.fst st j 0)).contains = true := by decide +kernel
  obtain ⟨hs, hr⟩ := table st j hj
  exact copy_span hs hr (fun _ _ => rfl)

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
