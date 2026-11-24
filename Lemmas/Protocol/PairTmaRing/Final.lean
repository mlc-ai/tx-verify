-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Faults

@[expose] public section

/-! # A pair TMA ring slot's barriers at the end of an execution

A proof tool. Under `Hyp`, the final phase of producer `a`'s empty barrier is its successful
polls `N` or one less (`empty_final_phase`): its poll for use `N - 1` found phase `N - 1`, and
the barrier's notifications are of uses below `N`, `nc` per use. The final phase of the full
barrier is a consumer's successful polls or one more (`full_final_phase`): its last poll found
that phase, and the barrier's arrivals are of uses at most that count (`full_units_le`). -/

namespace PTX.PairTmaRing

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
variable {nc : Nat} {S : Slot nc}

/-- The final phase of producer `a`'s empty barrier is its poller's successful polls `N` or one
less. -/
theorem empty_final_phase (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) {a : Fin 2}
    {before : State}
    (hst : stateBefore (X.objects (S.empty a))
      (X.objects (S.empty a)).length = some before) :
    okPolls (S.empty a) (X.tr (S.prod a)) ≤ before.phase + 1 ∧
      before.phase ≤ okPolls (S.empty a) (X.tr (S.prod a)) := by
  classical
  set log := X.objects (S.empty a) with hlog
  have hch : CheckedLog log := X.objects_checked hX _
  have hni : NoInval log := H.empty_noInval a
  set N := okPolls (S.empty a) (X.tr (S.prod a)) with hN
  constructor
  · by_contra hlt
    obtain ⟨k, w, sk, hk, -, -, hsk, hskp, -⟩ := E_found hX H (a := a)
      (n := N - 1) (by omega) (by omega)
    obtain ⟨t, htk, hle⟩ := hch.phase_mono hni (List.getElem?_eq_some_iff.mp hk).1.le
        (le_refl _) hsk
    rw [hst] at htk
    cases htk
    omega
  · have hexp := expected_of_init hX (H.empty_init a) (H.empty_noInval a) hst
    obtain ⟨hpend, hacc⟩ := (hch.accounted hni (le_refl _)).2 before hst
    have hu := MbarRing.Round.units_le_of_uses hch (fun y : Fin nc × Nat => note X S y.1 a y.2)
      (SE X S a) (i := log.length)
      (fun k r c' tx hr hf ha => (empty_count H k r c' tx hr hf ha).1)
      (fun k _ r' c' tx hr' hf' ha' => (empty_count H k r' c' tx hr' hf' ha').2)
    have hc := MbarRing.Round.card_le_of_uses (SE X S a) (Q := N)
      (fun y hy => by have := SE_use_lt hX H hy a; omega)
    simp only [Fintype.card_fin] at hc
    rw [hexp] at hpend hacc
    have : nc * before.phase ≤ nc * N := by
      have : nc * (before.phase + 1) = nc * before.phase + nc := by ring
      omega
    exact Nat.le_of_mul_le_mul_left this H.nc_pos

/-- The arrival units of the full barrier are at most one more than a consumer's successful
polls. -/
theorem full_units_le (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) (b : Fin nc) (i : Nat) :
    unitsBefore (X.objects (S.full)) i ≤
      okPolls (S.full) (X.tr (S.cons b)) + 1 := by
  have h := MbarRing.Round.units_le_of_uses (X.objects_checked hX (S.full))
    (fun y : Unit × Nat => itF X S ⟨0, by omega⟩ y.2)
    (Finset.univ ×ˢ Finset.range (okPolls (S.full) (X.tr (S.cons b)) + 1))
    (i := i) (fun k r c' tx hr hf ha => (full_count H k r c' tx hr hf ha).1)
    (fun k _ r' c' tx hr' hf' ha' => by
      obtain ⟨-, x, hx, hid'⟩ := full_count H k r' c' tx hr' hf' ha'
      obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
      have hx0' : x.1 = ⟨0, by omega⟩ := by simpa using hx0
      refine ⟨((), x.2), Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (by have := SF_use_le hX H hxS b; omega)⟩, ?_⟩
      rw [hid', hx0'])
  simpa using h

/-- The final phase of the full barrier is a consumer's successful polls `n` or one more. -/
theorem full_final_phase (hX : Consistent L K A mem0 X) (H : Hyp L K A X S) (b : Fin nc)
    {before : State}
    (hst : stateBefore (X.objects (S.full))
      (X.objects (S.full)).length = some before) :
    okPolls (S.full) (X.tr (S.cons b)) ≤ before.phase ∧
      before.phase ≤ okPolls (S.full) (X.tr (S.cons b)) + 1 := by
  set log := X.objects (S.full) with hlog
  have hch : CheckedLog log := X.objects_checked hX _
  have hni : NoInval log := H.full_noInval
  set n := okPolls (S.full) (X.tr (S.cons b)) with hn
  constructor
  · by_contra hlt
    obtain ⟨k, w, sk, hk, -, -, hsk, hskp, -⟩ := F_found hX H (b := b)
      (j := n - 1) (by omega)
    obtain ⟨t, htk, hle⟩ := hch.phase_mono hni (List.getElem?_eq_some_iff.mp hk).1.le
        (le_refl _) hsk
    rw [hst] at htk
    cases htk
    omega
  · have hexp := expected_of_init hX H.full_init H.full_noInval hst
    obtain ⟨hpend, hacc⟩ := (hch.accounted hni (le_refl _)).2 before hst
    have hu : unitsBefore log log.length ≤ n + 1 := full_units_le hX H b
      log.length
    rw [hexp] at hpend hacc
    omega

end
end PTX.PairTmaRing
