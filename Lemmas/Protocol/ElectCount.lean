-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # The lanes of a warp make equally many full-mask elections

A proof tool. When every election names the full member mask, each election of a lane `h` has a
partner of every other lane `g` of its warp in its instance (DEP-WARP-ELECT), with the same ordinal
among the lanes' elections (`ElectOrd.ordinal_eq`). So `g` has made at least as many elections as
`h` (`electCount_le`): the partner of `h`'s last election is `g`'s election of that ordinal. -/

namespace PTX

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The full member mask names every lane of a thread. -/
theorem electMember_full (L : Launch) (g : Nat) : electMember 4294967295 (laneOf L g) := by
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  revert hl
  generalize laneOf L g = lane
  revert lane
  decide

/-- **A lane has made at least as many elections as any lane of its warp**, when every
election names the full member mask. -/
theorem electCount_le (hX : Consistent L K A mem0 X)
    (hfull : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l → mask = 4294967295)
    {g h : Nat} (hs : SameWarp L h g) :
    (X.tr h).countP isElectEv ≤ (X.tr g).countP isElectEv := by
  set E := (X.tr h).countP isElectEv with hE
  rcases Nat.eq_zero_or_pos E with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  obtain ⟨y, -, ev, hev, hq, hcnt⟩ := Flow.exists_nth isElectEv (X.tr h) (n := E - 1)
    (k := (X.tr h).length) (by rw [List.take_length]; omega)
  obtain ⟨pc, mask, inst, l, rfl⟩ : ∃ pc mask inst l, ev = ⟨pc, .elect mask inst l⟩ := by
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> simp_all [isElectEv]
  have hel : X.Elect (h, y) pc mask inst l := hev
  have hmem : ∀ {f : Nat}, ∀ j pc mask inst l, X.Elect (f, j) pc mask inst l →
      ∀ k, electMember mask (laneOf L k) := by
    intro f j pc mask inst l he k
    rw [hfull he]
    exact electMember_full L k
  obtain ⟨x, hp⟩ := ElectOrd.partner hX hs hel (hmem _ _ _ _ _ hel g)
  have heq := ElectOrd.ordinal_eq hX hs (fun j pc mask inst l he => hmem j pc mask inst l he g)
    (fun j pc mask inst l he => hmem j pc mask inst l he h) hp
  obtain ⟨_, qc, _, nask, _, _, k, _, hx⟩ := hp
  have h1 := ElectOrd.elections_succ hx
  have h2 := Flow.countP_take_mono isElectEv (X.tr g)
    (show x + 1 ≤ (X.tr g).length from ElectOrd.lt_len hx)
  rw [List.take_length] at h2
  simp only [elections] at h1 heq
  omega

end
end PTX
