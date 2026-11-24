-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ElectMask
public import Lemmas.Flow.ElectLead
public import Lemmas.Flow.PollRendezvous

@[expose] public section

/-! # Two lanes' polls met through a warp collective

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/PollMeet.lean`): of two
lanes `g`, `h` of a warp, if `h` has made more collectives of a kind before its event at `k'` than
`g` before its event at `k`, and `g`'s event at `k` is no such collective, then `g`'s collective of
the ordinal `g` had reached at `k` comes after `k` and is one instance with `h`'s of that ordinal,
so it precedes `h`'s event in the execution-dependency order (`PollBefore`):

* `meet_shfl`: by shuffles (DEP-WARP-INSTANCE; a lane takes part or exited before, so `g` must
  not have exited with that many shuffles, `ShflExited`);
* `meet_elect`: by full-mask elections (every member lane takes part, `ElectOrd.partner`, at the
  same ordinal, `electOrdinal`). -/

namespace PTX.Flow
open PTX

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {m : Mem0} {X : Execution}

theorem count_after {p : Event → Bool} {g k a : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hne : p e = false) (ha : ((X.tr g).take a).countP p = ((X.tr g).take k).countP p)
    (hpa : ∃ ea, X.get (g, a) = some ea ∧ p ea = true) : k < a := by
  obtain ⟨ea, hea, hpe⟩ := hpa
  rcases Nat.lt_trichotomy k a with h | h | h
  · exact h
  · subst h; rw [he] at hea; cases hea; rw [hne] at hpe; cases hpe
  · have h1 := countP_take_succ hea hpe
    have h2 := countP_take_mono p (X.tr g) (show a + 1 ≤ k by omega)
    omega

theorem pos_before {p : Event → Bool} {g k' b : Nat} {n : Nat}
    (hn : ((X.tr g).take b).countP p = n)
    (hk' : n + 1 ≤ ((X.tr g).take k').countP p) : b < k' := by
  by_contra hge
  have := countP_take_mono p (X.tr g) (show k' ≤ b by omega)
  omega

/-- **Met through shuffles.** -/
theorem meet_shfl (hX : Consistent L K A m X) (hord : ElectOrdinal L X) {g h k k' c : Nat}
    {e : Event} (hw : SameWarp L g h) (he : X.get (g, k) = some e)
    (hne : Execution.isShfl e = false) (hc : ((X.tr g).take k).countP Execution.isShfl = c)
    (hh : c + 1 ≤ ((X.tr h).take k').countP Execution.isShfl) (hk' : k' < (X.tr h).length)
    (hex : ¬ ShflExited X g c) : PollBefore L K X (g, k) (h, k') := by
  have hcnt : c + 1 ≤ (X.tr h).countP Execution.isShfl := by
    have := countP_take_mono Execution.isShfl (X.tr h) (show k' ≤ (X.tr h).length by omega)
    rw [List.take_length] at this
    omega
  obtain ⟨b, hb⟩ := Step.exists_shflK (X := X) hcnt
  obtain ⟨⟨pcb, mb, ab, bb, cb, rb, ob, hgetb⟩, hnb⟩ := id hb
  have hbk : b < k' := pos_before hnb hh
  rcases Step.shfl_lane_of_ready hX hgetb hb hw.symm with ⟨a, ha⟩ | hx
  · obtain ⟨⟨pca, ma, aa, ba, ca, ra, oa, hgeta⟩, hna⟩ := id ha
    have hka : k < a := count_after he hne (hna.trans hc.symm)
      ⟨_, hgeta, by simp [Execution.isShfl]⟩
    exact ⟨a, hka, coll_depBefore (c := (false, c)) hX hord hw ha hb hbk hk'⟩
  · exact absurd hx hex

/-- **Met through full-mask elections.** -/
theorem meet_elect (hX : Consistent L K A m X) (hord : ElectOrdinal L X) {g h k k' c : Nat}
    {e : Event} (hw : SameWarp L g h) (he : X.get (g, k) = some e)
    (hne : isElectEv e = false) (hc : elections X g k = c)
    (hh : c + 1 ≤ elections X h k') (hk' : k' < (X.tr h).length)
    (hfull : ∀ {i : EvId} {pc mask inst l}, X.Elect i pc mask inst l → mask = 4294967295) :
    PollBefore L K X (g, k) (h, k') := by
  have hcnt : c + 1 ≤ (X.tr h).countP isElectEv := by
    have := countP_take_mono isElectEv (X.tr h) (show k' ≤ (X.tr h).length by omega)
    rw [List.take_length] at this
    unfold elections at hh
    omega
  obtain ⟨b, x, hx, hp, hcb⟩ := MbarRing.Slot.exists_nth_countP isElectEv hcnt
  obtain ⟨pcx, kx⟩ := x
  cases kx with
  | elect mask inst l =>
    have hgetb : X.get (h, b) = some ⟨pcx, .elect mask inst l⟩ := hx
    have hEb : X.Elect (h, b) pcx mask inst l := hgetb
    have hbk : b < k' := pos_before hcb (by unfold elections at hh; omega)
    have hm : electMember mask (laneOf L g) := by
      rw [hfull hEb]
      have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
      revert hl
      generalize laneOf L g = lane
      revert lane
      decide
    obtain ⟨a, hpar⟩ := ElectOrd.partner hX hw.symm hEb hm
    obtain ⟨p1, p2, m1, m2, i1, l1, l2, h1, h2⟩ := hpar
    have hord' := hord hw.symm h1 h2
    have hna : elections X g a = c := by
      unfold elections
      rw [← hord']
      exact hcb
    have hka : k < a := count_after (p := isElectEv) he hne (by unfold elections at hna hc; omega)
      ⟨_, h2, by simp [isElectEv]⟩
    have h2' := h2
    rw [hfull h2] at h2'
    have hEb' := hEb
    rw [hfull hEb] at hEb'
    exact ⟨a, hka, coll_depBefore (c := (true, c)) hX hord hw ⟨⟨_, _, _, h2'⟩, hna⟩
      ⟨⟨_, _, _, hEb'⟩, by unfold elections; exact hcb⟩ hbk hk'⟩
  | _ => simp [isElectEv] at hp

end
end PTX.Flow
