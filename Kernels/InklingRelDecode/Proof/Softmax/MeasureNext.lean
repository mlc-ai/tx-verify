-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Measure

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow Control

set_option maxRecDepth 100000

private theorem loop_upper (e : Entry) (t i : Nat) (v : Carry) :
    measure e ⟨loopSite e t i,i,v⟩ ≤ 91*(e.limit-i)+90 := by
  unfold loopSite; split_ifs <;> simp only [measure,Site.position] <;> omega

theorem measure_next {e L g d dn ev} (hi : Inv e (g%L.block) d)
    (h : Control.next e L g d ev = some (some dn)) :
    measure e dn + ev.counts.toNat ≤ measure e d := by
  have cnt : ev.counts.toNat ≤ 1 := by cases ev.counts <;> decide
  obtain ⟨s,i,v⟩ := d
  cases s with
  | arrive | bar21 =>
    have lt := hi.loop nofun nofun nofun (fun _ => nofun)
    simp only [Control.next] at h
    repeat' split at h
    all_goals cases h
    all_goals first
      | (apply Nat.le_trans (Nat.add_le_add (loop_upper ..) cnt); simp only [measure,Site.position]
         change i<e.limit at lt; omega)
      | (simp only [measure,Site.position]; omega)
  | pre j =>
    cases h
    by_cases bound : j.val+1<64
    · simp only [dite_eq_left bound,measure]; omega
    · simp only [dite_eq_right bound]
      exact Nat.le_trans (Nat.add_le_add (loop_upper ..) cnt) (by
        change _ ≤ 91*(e.limit-i)+(154-j.val); omega)
  | bar0 =>
    cases h
    by_cases enabled : preEnabled e (g%L.block)
    · simp only [enabled,↓reduceIte,measure]; omega
    · simp only [Bool.not_eq_true] at enabled
      simp only [enabled,Bool.false_eq_true,↓reduceIte]
      exact Nat.le_trans (Nat.add_le_add (loop_upper ..) cnt) (by
        change _ ≤ 91*(e.limit-i)+155; omega)
  | waitS | waitO =>
    obtain ⟨p,k⟩ := ev
    cases k with
    | wait l q ok a sc =>
      cases ok <;> cases h <;> simp [measure,Site.position,Event.counts]
    | _ => cases h
  | epilogue => cases h
  | _ =>
    simp only [Control.next] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals simp only [measure,Site.position]
    all_goals omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax
