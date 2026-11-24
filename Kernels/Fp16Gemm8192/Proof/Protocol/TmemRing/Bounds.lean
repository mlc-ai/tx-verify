-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Order

@[expose] public section

/-! # The accumulator ring's barriers at the end of the history

Bounds on a buffer's barriers after all their records, from the ring of items. A counted
notification of use `s` follows the producer's `s + 1`-th successful empty poll
(`fullItems_poll`), and one of use `s ≥ 1` follows consumer `b`'s `s`-th successful full poll
(`fullItems_cons`); a counted arrival of use `t` follows the producer's `t + 1`-th successful
empty poll (`emptyItems_poll`). So the empty barrier's phase is at most the producer's
successful polls (`empty_phase_le`), and a full barrier's phase at most one more than its
consumer's (`full_phase_le`). Every arrival of a consumer's trace is a counted arrival
(`emptyItems_of_arrival`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace TmemRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A counted notification of use `s` follows the producer's `s + 1`-th successful empty
poll. -/
theorem fullItems_poll (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j k : Fin 2} {x : Fin 1 × Nat}
    (hx : x ∈ fullItems L X c j k) :
    x.2 < okPolls ((slot L c j).empty 0) (X.tr (producer L X c j)) := by
  obtain ⟨pc, sp, he, htg, -, hc⟩ := fullItems_commit hpre hX ht hx
  have hg := commit_guard hpre hX ht he htg (n := x.2) (by rw [hc])
  exact (MbarRing.Poll.nth_present (X := X)).mp (MbarRing.Round.Slot.present_of_guard hg)

/-- A counted arrival of use `t` follows the producer's `t + 1`-th successful empty poll. -/
theorem emptyItems_poll (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {y : Fin 256 × Nat}
    (hy : y ∈ emptyItems L X c j) :
    y.2 < okPolls ((slot L c j).empty 0) (X.tr (producer L X c j)) := by
  have hgM := (ring hpre hX ht c j).guardM 0 y hy y.2 le_rfl
  obtain ⟨hx, -⟩ := (ring hpre hX ht c j).observes_full hX.depAcyclic
    (MbarRing.Round.Slot.present_of_guard hgM) 0
  exact fullItems_poll hpre hX ht hx

/-- A counted notification of use `s ≥ 1` on consumer `b`'s full barrier follows `b`'s `s`-th
successful full poll. -/
theorem fullItems_cons (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {x : Fin 1 × Nat}
    (hx : x ∈ fullItems L X c j ((slot L c j).owner b)) :
    x.2 ≤ okPolls ((slot L c j).full ((slot L c j).owner b)) (X.tr (consumerOf L c j b)) := by
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · omega
  have hg := (ring hpre hX ht c j).guardP _ x hx x.2 hpos le_rfl
  obtain ⟨hy, -⟩ := (ring hpre hX ht c j).observes_empty hX.depAcyclic (n := x.2 - 1)
    (by rw [Nat.sub_add_cancel hpos]; exact MbarRing.Round.Slot.present_of_guard hg) b
  have hgM := (ring hpre hX ht c j).guardM 0 (b, x.2 - 1) hy (x.2 - 1) le_rfl
  have := (MbarRing.Poll.nth_present (X := X)).mp (MbarRing.Round.Slot.present_of_guard hgM)
  simp only at this
  omega

/-- The arrival units of a buffer's barrier, by its fault-free arrivals' positions. -/
theorem units_card {j : Fin 2} {m : Loc} (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {f : Bool} {cta : Nat} (hm : m = Bar.loc L cta ⟨.acc, j.val, f⟩) :
    unitsBefore (X.objects m) (X.objects m).length =
      ((Finset.range (X.objects m).length).filter
        (fun i => ((X.objects m)[i]?).any isArrival = true)).card := by
  subst hm
  rw [unitsBefore, units_eq_isArrival hX ht _ (fun r hr => List.mem_of_mem_take hr),
    MbarRing.Slot.countP_take_card]

/-- **The empty barrier's phase.** After all its records, buffer `j`'s empty barrier has
completed at most as many phases as the producer's successful polls of it. -/
theorem empty_phase_le (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {st : State}
    (hst : stateBefore (X.objects ((slot L c j).empty 0))
      (X.objects ((slot L c j).empty 0)).length = some st) :
    st.phase ≤ okPolls ((slot L c j).empty 0) (X.tr (producer L X c j)) := by
  have hch := X.objects_checked hX ((slot L c j).empty 0)
  have hni := objects_noInval hX ht ((slot L c j).empty 0)
  obtain ⟨hp, hu⟩ := (hch.accounted hni le_rfl).2 st hst
  have hexp := expected_eq (cta := 2 * c) (f := false) hpre hX ht _ st hst
  change st.expected = 256 at hexp
  have hle := MbarRing.Round.units_le_of_uses hch
    (fun y : Fin 256 × Nat => arriveRef L X c j y.1 y.2) (emptyItems L X c j)
    (i := (X.objects ((slot L c j).empty 0)).length)
    (fun k' r' n tx' hr' hf' ha' => (empty_count hpre hX ht k' r' n tx' hr' hf' ha').1)
    (fun k' _ r' n tx' hr' hf' ha' => (empty_count hpre hX ht k' r' n tx' hr' hf' ha').2)
  have hc := MbarRing.Round.card_le_of_uses (emptyItems L X c j)
    (Q := okPolls ((slot L c j).empty 0) (X.tr (producer L X c j)))
    (fun y hy => emptyItems_poll hpre hX ht hy)
  simp only [Fintype.card_fin] at hc
  rw [hexp] at hp hu
  have : 256 * st.phase ≤ 256 * okPolls ((slot L c j).empty 0) (X.tr (producer L X c j)) := by
    rw [Nat.mul_succ] at hu
    omega
  exact Nat.le_of_mul_le_mul_left this (by norm_num)

/-- **A full barrier's phase.** After all its records, consumer `b`'s full barrier has
completed at most one more phase than `b`'s successful polls of it. -/
theorem full_phase_le (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {st : State}
    (hst : stateBefore (X.objects ((slot L c j).full ((slot L c j).owner b)))
      (X.objects ((slot L c j).full ((slot L c j).owner b))).length = some st) :
    st.phase ≤ okPolls ((slot L c j).full ((slot L c j).owner b))
      (X.tr (consumerOf L c j b)) + 1 := by
  have hch := X.objects_checked hX ((slot L c j).full ((slot L c j).owner b))
  have hni := objects_noInval hX ht ((slot L c j).full ((slot L c j).owner b))
  obtain ⟨hp, hu⟩ := (hch.accounted hni le_rfl).2 st hst
  have hexp := expected_eq (cta := 2 * c + b.val / 128) (f := true) hpre hX ht _ st hst
  change st.expected = 1 at hexp
  have hle := MbarRing.Round.units_le_of_uses hch
    (fun x : Fin 1 × Nat => notifyRef L X c j ((slot L c j).owner b) x.2)
    (fullItems L X c j ((slot L c j).owner b))
    (i := (X.objects ((slot L c j).full ((slot L c j).owner b))).length)
    (fun k' r' n tx' hr' hf' ha' => (full_count hpre hX ht k' r' n tx' hr' hf' ha').1)
    (fun k' _ r' n tx' hr' hf' ha' => by
      obtain ⟨-, x, hx, hid⟩ := full_count hpre hX ht k' r' n tx' hr' hf' ha'
      exact ⟨x, (Finset.mem_filter.mp hx).1, hid⟩)
  have hc := MbarRing.Round.card_le_of_uses (fullItems L X c j ((slot L c j).owner b))
    (Q := okPolls ((slot L c j).full ((slot L c j).owner b)) (X.tr (consumerOf L c j b)) + 1)
    (fun x hx => Nat.lt_succ_of_le (fullItems_cons hpre hX ht hx))
  simp only [Fintype.card_fin] at hc
  rw [hexp] at hp hu
  omega

/-- An arrival of consumer `b`'s trace on the empty barrier is a counted arrival. -/
theorem emptyItems_of_arrival (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} {b : Fin 256} {t : Nat}
    (h : t < arrivals ((slot L c j).empty 0) (X.tr (consumerOf L c j b))) :
    (b, t) ∈ emptyItems L X c j := by
  classical
  have h' : t + 1 ≤ ((X.tr (consumerOf L c j b)).take (X.tr (consumerOf L c j b)).length).countP
      (arrivesOn ((slot L c j).empty 0)) := by
    rw [List.take_length]; exact h
  obtain ⟨hlt, e, he, hp⟩ := nthEv_lt h'
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | arrive m tx cnt rel sc =>
    have hm : m = (slot L c j).empty 0 := by simpa [sourceArrive] using hp
    subst hm
    have hact : objectAction X X.async ((slot L c j).empty 0) (arriveRef L X c j b t) =
        some (.arrive cnt tx) := by simp [arriveRef, arriveAt, objectAction, he]
    obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 _).2.2 _ _ hact
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨mem_allCons b,
      Finset.mem_range.mpr ?_⟩, r, hr, hid, fault_free hpre hX ht c j
        ((slot L c j).empty_mem 0) r hr⟩
    have h1 : t ≤ arrivals ((slot L c j).empty 0) (X.tr (consumerOf L c j b)) := h.le
    have h2 : arrivals ((slot L c j).empty 0) (X.tr (consumerOf L c j b)) ≤
        (X.tr (consumerOf L c j b)).length := List.countP_le_length
    have h3 := len_le_consBound L X c j b
    simp only
    omega
  | _ => simp [sourceArrive] at hp

/-- Distinct counted arrivals have distinct records. -/
theorem arriveRef_inj (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {j : Fin 2} :
    Set.InjOn (fun y : Fin 256 × Nat => arriveRef L X c j y.1 y.2) (emptyItems L X c j) := by
  intro y hy y' hy' he
  simp only [arriveRef, Ref.thread.injEq, Prod.mk.injEq] at he
  have hb := consumerOf_inj (L := L) (by rw [hpre.block]; omega) he.1
  obtain ⟨-, -, -, h1, hc1⟩ := emptyItems_arrive hX ht hy
  obtain ⟨-, -, -, h2, hc2⟩ := emptyItems_arrive hX ht hy'
  have h2' : arriveAt L X c j y'.1 y.2 = arriveAt L X c j y'.1 y'.2 := hb ▸ he.2
  rw [hb, h2'] at hc1
  exact Prod.ext hb (hc1.symm.trans hc2)

/-- A counted arrival's record is a fault-free arrival without bytes. -/
theorem emptyItems_record (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {c : Nat} {j : Fin 2} {y : Fin 256 × Nat} (hy : y ∈ emptyItems L X c j) :
    ∃ (i : Nat) (r : Record Ref), (X.objects ((slot L c j).empty 0))[i]? = some r ∧
      r.id = arriveRef L X c j y.1 y.2 ∧
      isArrival r = true := by
  obtain ⟨r, hr, hid, hf⟩ := emptyItems_mem hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨pc, rel, sc, he, -⟩ := emptyItems_arrive hX ht hy
  have h := ((hX.tma.2.2.1 _).2.1 r hr).1
  rw [hid, arriveRef] at h
  simp [objectAction, he] at h
  exact ⟨i, r, hi, hid, (isArrival_iff r).mpr ⟨h.symm, hf⟩⟩

end TmemRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
