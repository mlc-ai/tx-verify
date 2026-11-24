-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.ElectOrdinal
public import Lemmas.Protocol.CountNth

@[expose] public section

/-! # No lane of a warp is ahead of another in elections

A proof tool (promoted from tml-fa4's `Proof2/Top/MmaLagLd.lean`, `elect_le`). When every
election of the kernel uses the full mask, every election of a lane `c` has a partner of each
other lane `g` of its warp in its instance (`ElectOrd.partner`), at the same ordinal
(`electOrdinal`). So `c`'s elections before any of its events are at most `g`'s elections over
its whole trace (`ElectOrd.elections_le`). A lane that commits or releases after its `k`-th
election is then bounded by another lane's progress (tml-fa4's MMA warp: the electing lane's
commits against another lane's polls). -/

namespace PTX

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **No lane has made more elections than another lane of its warp at the end of that lane's
trace**, when every election uses the full mask. -/
theorem ElectOrd.elections_le (hX : Consistent L K A mem0 X)
    (hfull : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l → mask = 4294967295)
    {c g : Nat} (hw : SameWarp L c g) (k : Nat) :
    elections X c k ≤ elections X g (X.tr g).length := by
  have hord : ElectOrdinal L X := electOrdinal hX (ElectMutual.of_full hfull)
  by_contra hlt
  push Not at hlt
  set e := elections X g (X.tr g).length with he
  have hcnt : e + 1 ≤ (X.tr c).countP isElectEv := by
    unfold elections at hlt
    have h2 : ((X.tr c).take k).countP isElectEv ≤ (X.tr c).countP isElectEv := by
      rcases le_or_gt k (X.tr c).length with h | h
      · have := Flow.countP_take_mono isElectEv (X.tr c) h
        rwa [List.take_length] at this
      · rw [List.take_of_length_le (by omega)]
    omega
  obtain ⟨b, ⟨pcx, kx⟩, hx, hp, hcb⟩ := MbarRing.Slot.exists_nth_countP isElectEv hcnt
  cases kx with
  | elect mask inst l =>
    have hEb : X.Elect (c, b) pcx mask inst l := hx
    have hm : electMember mask (laneOf L g) := by
      rw [hfull hEb]
      have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
      revert hl
      generalize laneOf L g = lane
      revert lane
      decide
    obtain ⟨a, hpar⟩ := ElectOrd.partner hX hw hEb hm
    obtain ⟨p1, p2, m1, m2, i1, l1, l2, h1, h2⟩ := hpar
    have hord := hord hw h1 h2
    have ha : a < (X.tr g).length := len_of_get h2
    have hsucc := Flow.countP_take_succ (p := isElectEv) h2 (by simp [isElectEv])
    have hmono := Flow.countP_take_mono isElectEv (X.tr g)
      (show a + 1 ≤ (X.tr g).length by omega)
    unfold elections at he
    simp only at hord
    omega
  | _ => simp [isElectEv] at hp

end
end PTX
