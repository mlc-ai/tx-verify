-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.RegionFrame
public import Lemmas.Flow.DivStep

@[expose] public section

/-! # A control segment inside a region keeps the facts the region does not write

A proof tool, generic over the kernel. `SegU.frameR` adds facts `H` to both ends of a control
segment (`SegU`) that lies in a region of code writing no register of `H` (`regionB`);
`SegU.sub_start` and `regionB_mono` restate a segment for start facts that contain its own. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A control segment keeps the facts its region does not write.** -/
theorem SegU.frameR (hA : RulesFrame A) {lo hi s q : Nat} {F G H : List (Nat × Value)}
    (h : SegU K A L g s F q G) (hB : regionB K lo hi (H.map Prod.fst) = true)
    (hS : ∀ pc, lo ≤ pc → pc ≤ hi → Assumption.SegFreePc A pc) (hlo : lo ≤ s) (hhi : s ≤ hi) :
    SegU K A L g s (F ++ H) q (G ++ H) := by
  intro t ht
  obtain ⟨htp, -, -, -, htF⟩ := id ht
  have hF := (holds_append _ _ _).mp htF
  rcases h t (At.mono ht hF.1) with ⟨u, hr, hu⟩ | hd
  · obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ := hu
    refine .inl ⟨u, hr, hu1, hu2, hu3, hu4, (holds_append _ _ _).mpr ⟨hu5, ?_⟩⟩
    refine holds_of_mem fun r v hm => ?_
    rw [region_frame hA hB hS hr (by omega) (by omega) r (List.mem_map_of_mem (f := Prod.fst) hm)]
    exact holds_mem hF.2 hm
  · exact .inr hd

/-- A segment from start facts that contain its own. -/
theorem SegU.sub_start {a b : Nat} {F F' G : List (Nat × Value)} (h : SegU K A L g a F b G)
    (hF : ∀ x ∈ F, x ∈ F') : SegU K A L g a F' b G :=
  fun t ht => h t (At.mono ht (holds_of_mem fun _ _ hm => holds_mem ht.2.2.2.2 (hF _ hm)))

/-- A region that writes no register of a list writes none of a sublist. -/
theorem regionB_mono {lo hi : Nat} {R R' : List Nat} (h : regionB K lo hi R = true)
    (hs : ∀ r ∈ R', r ∈ R) : regionB K lo hi R' = true := by
  unfold regionB at h ⊢
  simp only [List.all_eq_true] at h ⊢
  intro i hi'
  have h1 := h i hi'
  cases hc : K.code[lo + i]? with
  | none => rfl
  | some ins =>
    rw [hc] at h1
    by_cases hl : ins.op.isLocal = true
    · simp only [hl, ↓reduceIte, Bool.and_eq_true, List.all_eq_true] at h1 ⊢
      exact ⟨⟨fun r hr => h1.1.1 r (hs r hr), h1.1.2⟩, h1.2⟩
    · simpa [hl] using h1

end
end PTX.Flow.Code
