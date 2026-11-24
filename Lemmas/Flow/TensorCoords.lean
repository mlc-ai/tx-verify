-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TensorBox
public import Lemmas.Flow.TcTmpl

@[expose] public section

/-! # The origin of a tensor load's box

A proof tool. A unicast two-coordinate tensor load whose coordinate registers hold 32-bit values
below `2 ^ 31` has those values as its box's origin (`fires_cpTensor_origin2`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A 32-bit value below `2 ^ 31` reads back as itself. -/
theorem toInt_ofNat_lt32 {v : Nat} (h : v < 2 ^ 31) : (BitVec.ofNat 32 v).toInt = v := by
  rw [BitVec.toInt_ofNat', Int.bmod_def]
  have h1 : ((v : Int) % (2 ^ 32 : Nat)) = v := by
    rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
  push_cast at h1 ⊢
  rw [h1]
  split_ifs with h2
  · rfl
  · exfalso; omega

/-- **A tensor load's origin** is the values of its two coordinate registers. -/
theorem fires_cpTensor_origin2 {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {grp : Bool} {dst mb r0 r1 : Nat} {off moff : Int} {map : Opnd} {lm : TensorMode}
    {pc : Nat} {e : Event} {v0 v1 : Nat}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor true grp dst off map [.reg r0, .reg r1] mb moff
      none lm)) e (some u))
    (h0 : t.regs r0 = some (b32 v0)) (h1 : t.regs r1 = some (b32 v1)) (hv0 : v0 < 2 ^ 31)
    (hv1 : v1 < 2 ^ 31) :
    ∀ a s, e.kind = .tensorIssue a s → ∀ i : Fin (s.outer + 1),
      s.origin i = if i.val = 0 then (v0 : Int) else if i.val = 1 then (v1 : Int) else 0 := by
  intro a s hk
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor true grp dst off map [.reg r0, .reg r1] mb moff
      none lm)) e (some u) := hf
  rcases tensorTmpl_cpTensor_unicast (L := L) (g := g) (t := t) (ca := true) (grp := grp)
    (dst := dst) (mb := mb) (off := off) (moff := moff) (map := map) (cs := [.reg r0, .reg r1])
    (lm := lm) with ⟨f, hT⟩ | ⟨a', s', hT⟩
  · rw [hT] at hf'
    simp [Fires] at hf'
  · rw [hT] at hf'
    obtain ⟨rfl, -⟩ := hf'
    obtain ⟨hcopy, -⟩ := tensorTmpl_unicast_issue hT
    simp only [Kind.tensorIssue.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    unfold tensorLoadCopy at hcopy
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      List.mapM_cons, List.mapM_nil, readBits_b32 h0 (by omega),
        readBits_b32 h1 (by omega)] at hcopy
    rcases hm : tensorMap L g t map [.reg r0, .reg r1] lm with f | ⟨a'', outer, d⟩ <;>
      rw [hm] at hcopy
    · cases hcopy
    rcases hd : sharedEffAddr L g t true dst off with f | dl <;> simp only [hd] at hcopy
    · cases hcopy
    all_goals repeat' (split at hcopy <;> (try (cases hcopy; done)))
    all_goals cases hcopy
    all_goals intro i
    all_goals rcases i with ⟨_ | _ | i, hi⟩
    all_goals simp
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by omega)]; exact toInt_ofNat_lt32 hv0)
      | (rw [Nat.mod_eq_of_lt (by omega)]; exact toInt_ofNat_lt32 hv1)

end

end PTX.Flow
