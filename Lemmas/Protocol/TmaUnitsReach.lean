-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaUnitsBlock
public import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

/-! # Who blocks a poller of a TMA-fed full barrier with reuse paths

A proof tool: the `TmaUnits.Obj` counterpart of `Unit.Obj.reach_short`
(`Lemmas/Protocol/UnitReachBlocker.lean`, offset `δ = 0`), proved as there. The items of the
feeding thread `y` (its arrival and its `n` copies of a use) follow the polls of one consumer
thread `g` in the dependency order (`TmaUnits.Reach`: an item of use `t` follows `g`'s
successful polls with `j` earlier ones, for each `j < t`), and `g`'s successful polls alternate
with offset 0.

* **The final phase is at least the one `g`'s last poll found** (`Obj.okPolls_le`).
* **It is at most one use past `g`'s polls** (`Obj.phase_le`): an item of use `t ≥ 1` follows
  `g`'s poll with `t - 1` earlier ones, which is in `g`'s trace, so every counted item has a use at
  most `g`'s successful polls (`Obj.use_le_polls`); the arrivals have distinct uses, so the
  history holds
  at most that many plus one arrival units, while every completed phase holds one.
* **A blocked consumer's phase, and the feeder is short** (`Obj.reach_short`): when the final
  phase has the parity of `g`'s next poll it is `g`'s successful polls, and (`TmaUnits.Obj.short`)
  the feeder has made no more arrivals than it or fewer than `n` copies past it. -/

namespace PTX.MbarRing.TmaUnits

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {y n bytes : Nat}

/-- **The reuse of a TMA-fed full barrier as thread `g` polls it**: an item of use `t` follows,
in the dependency order, `g`'s polls for the uses before `t`. -/
def Reach (L : Launch) (K : Kernel) (_A : List Assumption) (X : Execution) (m : Loc)
    (y n bytes g : Nat) : Prop :=
  ∀ x ∈ S X m y n bytes, ∀ j < x.2,
    Relation.TransGen (DepStep L K X) (.thread (g, Poll.nth X m g j), true)
      (it X m y n x.1 x.2, false)

namespace Obj

/-- **The final phase is at least the one the last successful poll found.** -/
theorem okPolls_le (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) {g : Nat}
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) 0)
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before) :
    okPolls m (X.tr g) ≤ before.phase := by
  have hch := X.objects_checked hX m
  rcases Nat.eq_zero_or_pos (okPolls m (X.tr g)) with h0 | hpos
  · omega
  obtain ⟨k, w, -, hk, hwid, -, hww, -, hsel⟩ := MbarRing.Poll.record hX (o.counted.pclean hX)
    (show okPolls m (X.tr g) - 1 < okPolls m (X.tr g) by omega)
  have hs : objectThreadSelected g w.id = true := objectThreadSelected_iff.mpr ⟨_, hwid⟩
  obtain ⟨sw, hsw, hge, -⟩ := hch.selected_poll_phase_ge o.noInval _ (Nat.zero_le 1) hAlt hk hs
    hww
  obtain ⟨t, ht, hle⟩ := hch.phase_mono o.noInval (List.getElem?_eq_some_iff.mp hk).1.le le_rfl
    hsw
  rw [hst] at ht
  cases ht
  rw [hsel] at hge
  omega

/-- **Every counted item has a use at most the consumer's successful polls.** -/
theorem use_le_polls {g : Nat} (hR : Reach L K A X m y n bytes g) {x : Fin (n + 1) × Nat}
    (hx : x ∈ S X m y n bytes) : x.2 ≤ okPolls m (X.tr g) := by
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · omega
  have hpres := Unit.present_of_path (hR x hx (x.2 - 1) (by omega))
  have := MbarRing.Poll.nth_present.mp hpres
  omega

/-- **The final phase is at most one use past the consumer's polls**, when the consumer's polls
precede the feeder's items in the dependency order. -/
theorem phase_le (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) (hn : 0 < n) {g : Nat}
    (hR : Reach L K A X m y n bytes g) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before) :
    before.phase ≤ okPolls m (X.tr g) + 1 := by
  classical
  have hch := X.objects_checked hX m
  -- the history holds at most `n' + 1` arrival units
  have hunits : arrivalUnits (X.objects m) ≤ okPolls m (X.tr g) + 1 := by
    rw [arrivalUnits_eq_length (fun r hr c tx _ ha => by
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
        exact (o.arrive hk ha).1), ← List.countP_eq_length_filter,
      ← List.take_length (l := X.objects m), MbarRing.Slot.countP_take_card]
    calc _ ≤ (({0} : Finset (Fin (n + 1))) ×ˢ Finset.range (okPolls m (X.tr g) + 1)).card :=
          PairTmaRing.card_le_of_rel _ _
            (fun k x => ∃ r, (X.objects m)[k]? = some r ∧ r.id = it X m y n x.1 x.2)
            (fun k hk => ?_) (fun k _ k' _ x _ h1 h2 => by
              obtain ⟨r, hr, hid⟩ := h1
              obtain ⟨r', hr', hid'⟩ := h2
              exact ObjectInit.checked_record_index_eq hch hr hr' (hid.trans hid'.symm))
      _ = okPolls m (X.tr g) + 1 := by simp
    obtain ⟨-, hk'⟩ := Finset.mem_filter.mp hk
    obtain ⟨r, hr, hc⟩ : ∃ r, (X.objects m)[k]? = some r ∧ countedArrive r = true := by
      cases h : (X.objects m)[k]? with
      | none => rw [h] at hk'; simp at hk'
      | some r => rw [h] at hk'; exact ⟨r, rfl, by simpa using hk'⟩
    obtain ⟨hf, c, tx, ha⟩ := countedArrive_iff.mp hc
    obtain ⟨x, hx, h0, hid⟩ := o.rec_zero hn hr hf ha
    exact ⟨x, Finset.mem_product.mpr ⟨h0, Finset.mem_range.mpr
      (Nat.lt_succ_of_le (use_le_polls hR hx))⟩, r, hr, hid⟩
  -- while every completed phase holds one
  obtain ⟨hp, hacc⟩ := (hch.accounted o.noInval le_rfl).2 before hst
  simp only [unitsBefore, List.take_length] at hacc
  have hexp := PairTmaRing.expected_of_init hX o.init o.noInval hst
  rw [hexp] at hp hacc
  omega

/-- **A blocked consumer is at the final phase, and the feeder is short**: when the final phase
has the parity of the consumer's successful polls, it is that count, and the feeding thread has
made no more arrivals than it or fewer than `n` copies past it, when no tensor copy is open and
no record of the object faults. -/
theorem reach_short (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) (hn : 0 < n)
    {g : Nat} (hR : Reach L K A X m y n bytes g)
    (hAlt : SelectedAlternates (objectThreadSelected g) (X.objects m) 0)
    (hff : ∀ r ∈ X.objects m, r.fault = none) (hno : ¬ Descent.Obl L X .tensor)
    {before : State} (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hpar : before.phase % 2 = okPolls m (X.tr g) % 2) :
    before.phase = okPolls m (X.tr g) ∧ (arrivals m (X.tr y) ≤ before.phase ∨
      (X.tr y).countP (issuesTo m) < n * (before.phase + 1)) := by
  have h1 := o.okPolls_le hX hAlt hst
  have h2 := o.phase_le hX hn hR hst
  have hph : before.phase = okPolls m (X.tr g) := by omega
  refine ⟨hph, o.short hX hn hff hno hst fun x hx => ?_⟩
  rw [hph]
  exact use_le_polls hR hx

end Obj
end
end PTX.MbarRing.TmaUnits
