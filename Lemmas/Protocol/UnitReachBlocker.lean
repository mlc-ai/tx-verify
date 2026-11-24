-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitObjBlocker
public import Lemmas.Protocol.ObservedSync
public import Lemmas.Protocol.RecordCountPair

@[expose] public section

/-! # Who blocks a poller of a unit object with reuse paths

A proof tool for the progress of a unit object (`MbarRing.Unit.Obj`) whose producers' arrivals
follow the polls of one consumer thread `g` in the dependency order (`Unit.Reach`: producer `a`'s
arrival of use `t` follows `g`'s successful polls with `j + δ` earlier ones, for each `j < t`).

* **The final phase is one use ahead** (`Obj.reach_phase`): when the final phase `P` has the
  parity of `g`'s next poll (its `n` successful polls plus `δ`, with `δ ≤ n`), `P + δ = n`. The
  phase is at least the one `g`'s last successful poll found (`Obj.okPolls_le`). It is at most
  `n + 1 - δ` (`Obj.phase_le`): an arrival of use `t ≥ 1` follows `g`'s poll with `t - 1 + δ`
  earlier ones, which is in `g`'s trace, so every counted arrival has a use below `n - δ + 1`;
  the counted arrivals of one producer have distinct uses, so the history holds at most
  `N (n - δ + 1)` arrival units, while every completed phase holds `N`.
* **Some producer is short** (`Obj.reach_short`): when no record of the object faults, a
  thread's arrivals on it are at most its recorded arrivals (`arrivals_le_unitRec`), and some
  producer has recorded no more than `P` (`Obj.blocked`).
* **The final state** of a history initialized first (`PairTmaRing.InitFirst`) with a record
  exists (`final_of_init`). -/

namespace PTX.MbarRing.Unit

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

/-- The source of a dependency path from a poll's return is in its thread's trace. -/
theorem present_of_path {w : EvId} {n : Ref × Bool}
    (h : Relation.TransGen (DepStep L K X) (.thread w, true) n) :
    X.RefPresent (.thread w) := by
  obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.mp h
  exact hc.present_of_return

/-- A thread's arrivals on an object none of whose records faults are at most its recorded
arrivals. -/
theorem arrivals_le_unitRec (hX : Consistent L K A mem0 X)
    (hff : ∀ r ∈ X.objects m, r.fault = none) (h : Nat) :
    arrivals m (X.tr h) ≤ (X.objects m).countP (unitRec h) := by
  classical
  unfold arrivals
  refine countP_le_of_records (fun j => Ref.thread (h, j))
    (fun i j _ _ hf => by simpa using hf) (fun i hi => ?_)
  obtain ⟨⟨pc, kind⟩, he, hp⟩ := (mem_indicesP_iff _ _ i).mp hi
  cases kind with
  | arrive m' tx cnt rel sc =>
    have hm : m' = m := by simpa [arrivesOn, sourceArrive] using hp
    subst hm
    have hget : X.get (h, i) = some ⟨pc, .arrive m' tx cnt rel sc⟩ := he
    have hact : objectAction X X.async m' (Ref.thread (h, i)) = some (.arrive cnt tx) := by
      simp [objectAction, hget]
    obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 m').2.2 (Ref.thread (h, i)) _ hact
    have hact' := ((hX.tma.2.2.1 m').2.1 r hr).1
    rw [hid, hact] at hact'
    have hra : r.action = .arrive cnt tx := (Option.some.inj hact').symm
    refine ⟨r, hr, hid, ?_⟩
    simp only [unitRec, Bool.and_eq_true, Option.isNone_iff_eq_none]
    exact ⟨⟨objectThreadSelected_iff.mpr ⟨i, hid⟩, hff r hr⟩, by rw [hra]⟩
  | _ => simp [arrivesOn, sourceArrive] at hp

/-- **The final state of an object initialized first**, when its history has a record. -/
theorem final_of_init (hX : Consistent L K A mem0 X) {c : Nat}
    (hfirst : PairTmaRing.InitFirst X m c) (hni : NoInval (X.objects m))
    (hne : X.objects m ≠ []) :
    ∃ st, stateBefore (X.objects m) (X.objects m).length = some st := by
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨r0, h0, ha0, hf0, -⟩ := hfirst r hr
  obtain ⟨st, hst, -⟩ := ObjectInit.checked_expected_after_init (X.objects_checked hX m) hni
    h0 ha0 hf0 (List.length_pos_iff.mpr hne) le_rfl
  exact ⟨st, hst⟩

namespace Obj

/-- **The final phase is at least the one the last successful poll found.** -/
theorem okPolls_le (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) (g : Nat)
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before) :
    okPolls m (X.tr g) ≤ before.phase + δ := by
  have hch := X.objects_checked hX m
  rcases Nat.eq_zero_or_pos (okPolls m (X.tr g)) with h0 | hpos
  · omega
  obtain ⟨k, w, -, hk, hwid, -, hww, -, hsel⟩ := MbarRing.Poll.record hX (O.pclean hX)
    (show okPolls m (X.tr g) - 1 < okPolls m (X.tr g) by omega)
  have hs : objectThreadSelected g w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨sw, hsw, hge, -⟩ := hch.selected_poll_phase_ge O.noInval _ O.δ_le (O.alt hX g) hk hs
    hww
  obtain ⟨t, ht, hle⟩ := hch.phase_mono O.noInval (List.getElem?_eq_some_iff.mp hk).1.le le_rfl
    hsw
  rw [hst] at ht
  cases ht
  rw [hsel] at hge
  omega

/-- **The final phase is at most one use past the consumer's polls**, when the consumer's polls
precede the producers' arrivals in the dependency order. -/
theorem phase_le (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {g : Nat}
    (hR : Reach L K A X m N prod δ g) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hδ : δ ≤ okPolls m (X.tr g)) :
    before.phase + δ ≤ okPolls m (X.tr g) + 1 := by
  classical
  have hch := X.objects_checked hX m
  -- every counted arrival has a use below `n - δ + 1`
  have huse : ∀ x ∈ S X m prod, x.2 < okPolls m (X.tr g) - δ + 1 := by
    intro x hx
    rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
    · omega
    have hpres := present_of_path (hR x hx (x.2 - 1) (by omega))
    have := MbarRing.Poll.nth_present.mp hpres
    omega
  -- so the history holds at most `N (n - δ + 1)` arrival units
  have hunits : arrivalUnits (X.objects m) ≤ N * (okPolls m (X.tr g) - δ + 1) := by
    rw [arrivalUnits_eq_length (fun r hr c tx _ ha => by
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
        exact (O.arrive_rec hk ha).1), ← List.countP_eq_length_filter,
      ← List.take_length (l := X.objects m), MbarRing.Slot.countP_take_card]
    calc _ ≤ (Finset.univ ×ˢ Finset.range (okPolls m (X.tr g) - δ + 1) :
            Finset (Fin N × Nat)).card :=
          PairTmaRing.card_le_of_rel _ _
            (fun k x => ∃ r, (X.objects m)[k]? = some r ∧
              r.id = .thread (it X m prod x.1 x.2))
            (fun k hk => ?_) (fun k _ k' _ x _ h1 h2 => by
              obtain ⟨r, hr, hid⟩ := h1
              obtain ⟨r', hr', hid'⟩ := h2
              exact ObjectInit.checked_record_index_eq hch hr hr' (hid.trans hid'.symm))
      _ = N * (okPolls m (X.tr g) - δ + 1) := by simp
    obtain ⟨-, hk'⟩ := Finset.mem_filter.mp hk
    obtain ⟨r, hr, hc⟩ : ∃ r, (X.objects m)[k]? = some r ∧ countedArrive r = true := by
      cases h : (X.objects m)[k]? with
      | none => rw [h] at hk'; simp at hk'
      | some r => rw [h] at hk'; exact ⟨r, rfl, by simpa using hk'⟩
    obtain ⟨hf, c, tx, ha⟩ := countedArrive_iff.mp hc
    obtain ⟨x, hx, hid⟩ := O.rec_S hr hf ha
    exact ⟨x, Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (huse x hx)⟩,
      r, hr, hid⟩
  -- while every completed phase holds `N`
  obtain ⟨hp, hacc⟩ := (hch.accounted O.noInval le_rfl).2 before hst
  simp only [unitsBefore, List.take_length] at hacc
  have hexp := PairTmaRing.expected_of_init hX O.init O.noInval hst
  rw [hexp] at hp hacc
  rw [Nat.mul_succ] at hacc
  have hle : N * before.phase ≤ N * (okPolls m (X.tr g) - δ + 1) := by omega
  have := Nat.le_of_mul_le_mul_left hle O.pos
  omega

/-- **A blocked consumer is one use ahead**: when the final phase has the parity of the
consumer's next poll, it is the consumer's successful polls minus `δ`. -/
theorem reach_phase (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {g : Nat}
    (hR : Reach L K A X m N prod δ g) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hδ : δ ≤ okPolls m (X.tr g))
    (hpar : before.phase % 2 = (okPolls m (X.tr g) + δ) % 2) :
    before.phase + δ = okPolls m (X.tr g) := by
  have h1 := O.okPolls_le hX g hst
  have h2 := O.phase_le hX hR hst hδ
  omega

/-- **A blocked consumer is one use ahead, and some producer is short**: it has made no more
arrivals than the final phase, when no record of the object faults. -/
theorem reach_short (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {g : Nat}
    (hR : Reach L K A X m N prod δ g) (hff : ∀ r ∈ X.objects m, r.fault = none)
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hδ : δ ≤ okPolls m (X.tr g))
    (hpar : before.phase % 2 = (okPolls m (X.tr g) + δ) % 2) :
    before.phase + δ = okPolls m (X.tr g) ∧ ∃ a, arrivals m (X.tr (prod a)) ≤ before.phase := by
  refine ⟨O.reach_phase hX hR hst hδ hpar, ?_⟩
  obtain ⟨a, ha⟩ := O.blocked hX hst
  exact ⟨a, (arrivals_le_unitRec hX hff (prod a)).trans ha⟩

end Obj
end
end PTX.MbarRing.Unit
