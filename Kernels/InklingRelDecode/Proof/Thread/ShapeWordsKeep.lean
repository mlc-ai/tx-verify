-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAFlow

@[expose] public section

/-!
# The loaded request words survive the prologue

The prologue's three request words (`cu0`, `cu1`, `sk`) are set by its three loads and by no other
site (`ProA.next` changes only these three fields, the six block-table words, the elections and
the query values). Once all three are loaded (`Site.afterSk`) a step keeps them
(`keeps_next`) and the machine stays at sites after the loads (`afterSk_next`). The protocol
layer's proof that the loaded words are the request's (`MbarWords`) reads the words off the
loads and carries them through the rest of the prologue with these two facts.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A data record keeps the three request words. -/
def Keeps (dt dt' : Dat) : Prop := dt'.cu0 = dt.cu0 ∧ dt'.cu1 = dt.cu1 ∧ dt'.sk = dt.sk

/-- **A step from a site after the loads keeps the request words.** -/
theorem keeps_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hk : s.afterSk = true) :
    Keeps dt d'.dt := by
  cases s <;> first
    | exact absurd hk (by decide)
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h; subst h; simp_all [Keeps, elDt, qUpd]))

theorem qSite_afterSk {L : Launch} {g : Nat} (dt : Dat) {G : Nat} (hG : G ≤ 3) :
    (qSite L g dt G).afterSk = true :=
  (qSite_prop G hG).1

theorem qs0 {L : Launch} {g : Nat} (dt : Dat) : (qSite L g dt 0).afterSk = true :=
  qSite_afterSk dt (by decide)

theorem qs1 {L : Launch} {g : Nat} (dt : Dat) : (qSite L g dt 1).afterSk = true :=
  qSite_afterSk dt (by decide)

theorem qs2 {L : Launch} {g : Nat} (dt : Dat) : (qSite L g dt 2).afterSk = true :=
  qSite_afterSk dt (by decide)

theorem qs3 {L : Launch} {g : Nat} (dt : Dat) : (qSite L g dt 3).afterSk = true :=
  qSite_afterSk dt (by decide)

/-- **A step from a site after the loads stays after the loads.** -/
theorem afterSk_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hk : s.afterSk = true) :
    d'.site.afterSk = true := by
  cases s <;> first
    | exact absurd hk (by decide)
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h; subst h
            first | (simp only [qs0, qs1, qs2, qs3]; done) | rfl))

/-! ### The three loads -/

/-- A 32-bit word of the launch as a number. -/
theorem word32_b32 {x : Nat} (hx : x < 2 ^ 32) : word32 (b32 x) = some x := by
  have h64 : x < 2 ^ 64 := by omega
  simp only [word32, b32, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h64]
  simp only [ite_eq_left_iff, not_lt]
  omega

/-- **The first load sets `cu0`**: the event reads bytes that rebuild to a 32-bit word `x`, which
is the new `cu0`, and the machine moves to the second load. -/
theorem next_ldCu0 {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.ldCu0, dt⟩ e = some (some d')) :
    ∃ a bs v x, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧ word32 v = some x ∧
      d' = ⟨.ldCu1, { dt with cu0 := x }⟩ := by
  simp only [next] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; subst h
       exact ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, rfl⟩)

/-- **The second load sets `cu1`.** -/
theorem next_ldCu1 {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.ldCu1, dt⟩ e = some (some d')) :
    ∃ a bs v x, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧ word32 v = some x ∧
      d' = ⟨.ldSk, { dt with cu1 := x }⟩ := by
  simp only [next] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; subst h
       exact ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, rfl⟩)

/-- **The third load sets `sk`** (and the machine checks the words). -/
theorem next_ldSk {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.ldSk, dt⟩ e = some (some d')) :
    ∃ a bs v x, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧ word32 v = some x ∧
      d' = ⟨.el0, { dt with sk := x }⟩ := by
  simp only [next] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; subst h
       exact ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, rfl⟩)

/-- The step from `sMax` goes to the first load and keeps the data. -/
theorem next_sMax {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.sMax, dt⟩ e = some (some d')) : d' = ⟨.ldCu0, dt⟩ := by
  simp only [next, Option.some.injEq] at h
  exact h.symm

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
