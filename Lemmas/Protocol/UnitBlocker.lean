-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitGate
public import Lemmas.Protocol.MbarRingBlocker
public import Lemmas.Protocol.PairTmaRing.Blocker

@[expose] public section

/-! # Who blocks a poller of a gated unit object

A proof tool, instantiating `MbarRing.Blocker` for a gated unit object (`Unit.Gate`). The object's
transaction counter stays zero (`Obj.tx_zero`). A consumer `h` whose next poll of the object
(with the parity of its `n` successful polls plus `δ`) does not find the final phase `P` is one
use ahead: `P + δ = n` (`Gate.blocked`). The final phase is at least the one `h`'s last
successful poll found (`selected_poll_phase_ge`) and below `n + 2 - δ`, since phase `n + 1 - δ`
would hold its partner producer's arrival of that use, which a poll with `n` earlier ones of `h`
precedes in the dependency order. And some producer has exactly `P` counted arrivals
(`unitsOf`): every producer has one in each completed phase (`Obj.phase_all`), and phase `P`
lacks one (`MbarRing.Blocker.exists_eq`). -/

namespace PTX.MbarRing.Unit

open AsyncCopy Flow
open MBarrier hiding okPolls

noncomputable section

/-- Whether a record is a counted arrival of thread `g`. -/
def unitsOf (g : Nat) (r : Record Ref) : Bool := countedArrive r && objectThreadSelected g r.id

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

namespace Obj

/-- **A unit object's transaction counter stays zero.** -/
theorem tx_zero (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {j : Nat}
    (hj : j ≤ (X.objects m).length) {st : State} (hst : stateBefore (X.objects m) j = some st) :
    st.tx = 0 := by
  have hbal := (X.objects_checked hX m).tx_balance O.noInval hj hst
  have hz : ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects m) →
      expectedTxBytes xs = 0 ∧ completedTxBytes xs = 0 := by
    intro xs hxs
    induction xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons r rest ih =>
      have hr := hxs r List.mem_cons_self
      obtain ⟨h1, h2⟩ := ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))
      rw [expectedTxBytes, completedTxBytes, h1, h2]
      unfold Record.expectedTxBytes Record.completedTxBytes
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      cases ha : r.action with
      | arrive n tx =>
        obtain ⟨-, rfl, -⟩ := O.arrive_rec hk ha
        cases r.fault <;> simp
      | completeTx n =>
        exfalso
        cases O.src r hr with
        | init ha' => rw [ha] at ha'; cases ha'
        | poll _ _ ha' => rw [ha] at ha'; cases ha'
        | arrive _ _ _ ha' => rw [ha] at ha'; cases ha'
      | _ => cases r.fault <;> simp
  obtain ⟨h1, h2⟩ := hz _ (fun q hq => List.mem_of_mem_take hq)
  rw [hbal, h1, h2]
  rfl

end Obj

namespace Gate

variable {cons : Nat → Prop} {pair : Fin N → Nat → Prop}

open Classical in
/-- **A blocked poller is one use ahead, and some producer is short.** -/
theorem blocked (hX : Consistent L K A mem0 X) (G : Gate L K A X m N prod δ cons pair) {h : Nat}
    (hh : cons h) {before : State}
    (hst : stateBefore (X.objects m) (X.objects m).length = some before)
    (hpar : before.phase % 2 = (okPolls m (X.tr h) + δ) % 2) :
    before.phase + δ = okPolls m (X.tr h) ∧
      ∃ a, (X.objects m).countP (unitsOf (prod a)) = before.phase := by
  have hch := X.objects_checked hX m
  have hni := G.noInval
  have hδ := G.δ_le
  set n := okPolls m (X.tr h) with hn
  -- the final phase is below `n + 2 - δ`
  have hup : before.phase + δ ≤ n + 1 := by
    by_contra hgt
    obtain ⟨a, hpair⟩ := G.cover h hh
    obtain ⟨p, r, i, -, hp, -, ha, hid, -, hu⟩ := G.phase_all hX (j := (X.objects m).length)
      (q := n + 1 - δ) le_rfl hst (by omega)
      (fun p' _ r a i c tx hp hf ha hid hph => by
        have := G.phase_eq hX p' r a i c tx hp hf ha hid
        rw [hph] at this
        exact (Option.some.inj this).symm) a
    obtain ⟨pca, sca, hea⟩ := G.arrive_of_id hp ha hid
    obtain ⟨j, pcw, pw, acq, scw, hw, hcnt, -⟩ := G.gate hpair hea (by omega)
    have h1 := MbarRing.Poll.okPoll_get hw
    have h2 := MbarRing.Poll.okPolls_mono m (X.tr h) (show j + 1 ≤ (X.tr h).length from
      (List.getElem?_eq_some_iff.mp hw).1)
    rw [List.take_length] at h2
    omega
  -- and at least the phase the last successful poll found
  have hlo : n ≤ before.phase + δ := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · omega
    obtain ⟨pc, p, acq, sc, hw, hc⟩ := MbarRing.Poll.nth_spec (X := X) (m := m) (g := h)
      (n := n - 1) (by omega)
    obtain ⟨k, w, hk, -, hww, -, hsel, hsb⟩ := G.poll_record hX hw
    obtain ⟨sw, hsw, hge, -⟩ := hch.selected_poll_phase_ge hni _ hδ (G.alt hX h) hk hsel hww
    obtain ⟨t, ht, hle⟩ := hch.phase_mono hni (List.getElem?_eq_some_iff.mp hk).1.le le_rfl hsw
    rw [hst] at ht
    cases ht
    rw [hsb, hc] at hge
    omega
  have hout : before.phase + δ = n := by omega
  refine ⟨hout, ?_⟩
  -- some producer is short
  have hexp := PairTmaRing.expected_of_init hX G.init hni hst
  obtain ⟨a, -, ha⟩ := MbarRing.Blocker.exists_eq (hinc := G.noIncrement) hch hni hst
    (G.tx_zero hX le_rfl hst)
    (fun _ : Fin N => 1) (fun a => (X.objects m).countP (unitsOf (prod a))) (by simp [hexp])
    (by
      rw [arrivalUnits_eq_length (fun r hr c tx _ ha => by
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
        exact (G.arrive_rec hk ha).1), ← List.countP_eq_length_filter]
      simp only [Nat.one_mul]
      refine PairTmaRing.sum_countP_le _ _ _ (fun r _ a a' h1 h2 => ?_) (fun r _ a h1 => ?_)
      · simp only [unitsOf, Bool.and_eq_true] at h1 h2
        obtain ⟨j1, hj1⟩ := objectThreadSelected_iff.mp h1.2
        obtain ⟨j2, hj2⟩ := objectThreadSelected_iff.mp h2.2
        rw [hj1] at hj2
        simp only [Ref.thread.injEq, Prod.mk.injEq] at hj2
        exact G.inj hj2.1
      · simp only [unitsOf, Bool.and_eq_true] at h1
        exact h1.1)
    (fun a => by
      rw [← List.take_length (l := X.objects m), MbarRing.Slot.countP_take_card]
      refine le_trans (le_of_eq (Finset.card_range before.phase).symm)
        (PairTmaRing.card_le_of_rel (Finset.range before.phase) _
          (fun q k => ∃ r i, (X.objects m)[k]? = some r ∧ r.id = .thread (prod a, i) ∧
            arrivals m ((X.tr (prod a)).take i) = q)
          (fun q hq => ?_) (fun q _ q' _ k _ ⟨r, i, hr, hid, hu⟩ ⟨r', i', hr', hid', hu'⟩ => ?_))
      · obtain ⟨p, r, i, hp, hr, hf, hra, hid, -, hu⟩ := G.phase_all hX
          (j := (X.objects m).length) (q := q) le_rfl hst (Finset.mem_range.mp hq)
          (fun p' _ r a i c tx hp hf ha hid hph => by
            have := G.phase_eq hX p' r a i c tx hp hf ha hid
            rw [hph] at this
            exact (Option.some.inj this).symm) a
        refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, ?_⟩, r, i, hr, hid, hu⟩
        rw [hr]
        simp only [Option.any_some, unitsOf, Bool.and_eq_true]
        exact ⟨countedArrive_iff.mpr ⟨hf, 1, 0, hra⟩, objectThreadSelected_iff.mpr ⟨i, hid⟩⟩
      · rw [hr] at hr'
        have hrr := Option.some.inj hr'
        subst hrr
        rw [hid] at hid'
        simp only [Ref.thread.injEq, Prod.mk.injEq, true_and] at hid'
        subst hid'
        exact hu.symm.trans hu')
  exact ⟨a, ha⟩

end Gate
end
end PTX.MbarRing.Unit
