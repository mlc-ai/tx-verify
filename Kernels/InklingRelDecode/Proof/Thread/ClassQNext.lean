-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ClassQAddr

@[expose] public section

/-!
# The step at a query load

The prologue's step at query load `k` (`ProA.next` at `ldqSite k`) rebuilds the loaded bytes into a
two-byte value and stores it as `q k` (`next_ldq`); a load that returned such a value continues,
the machine does not stop (`next_ldq_some`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- **The step at query load `k`** stores the loaded two-byte value as `q k`. -/
theorem next_ldq {L : Launch} {g : Nat} {k : Nat} (hk : k < 64) {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨ldqSite k, dt⟩ e = some (some d')) :
    ∃ a bs v, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧ v.bytes = 2 ∧ d'.dt = qUpd dt k v := by
  interval_cases k
  all_goals
    simp only [ldqSite, ldqSites, List.getD_cons_zero, List.getD_cons_succ] at h
    simp only [next] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (simp only [Option.some.injEq] at h; subst h
         exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, rfl⟩)

/-- **A query load that returned a two-byte value continues**: the step is a successor. -/
theorem next_ldq_some {L : Launch} {g : Nat} {k : Nat} (hk : k < 64) {dt : Dat} {e : Event}
    {a : Acc} {bs : List (Option Byte)} {v : Value} (he : e.kind = .rd a bs)
    (hrb : rebuild 3 bs = .ok v) (hv : v.bytes = 2) :
    ∃ d', next L g ⟨ldqSite k, dt⟩ e = some (some d') := by
  interval_cases k
  all_goals
    simp only [ldqSite, ldqSites, List.getD_cons_zero, List.getD_cons_succ]
    simp only [next, he, hrb, hv, ↓reduceIte]
    exact ⟨_, rfl⟩

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
