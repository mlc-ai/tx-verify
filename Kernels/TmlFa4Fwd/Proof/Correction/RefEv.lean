-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.Correction.Ledger
import Kernels.TmlFa4Fwd.Proof.Correction.Ref
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The ledger classes of the correction warps' events

An event of the shape table at a state (`Ev`) that is no undefined behaviour and no failed poll
belongs to exactly the class `sig` of its site (`ev_cls`): the arrivals name their barrier by its
shared offset, the polls likewise, the CTA barriers are barrier 2 or the lane's named barrier `k`
(the two named barrier ids are 3 to 6 and 7 to 10, so they differ from each other and from 2),
and the stores are the vector-store and LSE sites' events. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g : Nat}

theorem bl_inj {a b : Nat} : bl L g a = bl L g b ↔ a = b := by
  simp [bl]

theorem nbOf_toNat (k : Fin 2) : (nbOf L g k).toNat =
    (Epilogue.andi (BitVec.ofNat 64 (g % L.block / 32)) 3).toNat + if k = 0 then 3 else 7 := by
  fin_cases k
  · exact nb_val _ 3 (by omega)
  · exact nb_val _ 7 (by omega)

theorem nbW_eq (k : Fin 2) : nbW L g k = nbOf L g k := by
  fin_cases k <;> rfl

theorem nb_inj (k k' : Fin 2) : (nbOf L g k).toNat = (nbOf L g k').toNat ↔ k = k' := by
  rw [nbOf_toNat, nbOf_toNat]
  fin_cases k <;> fin_cases k' <;> simp

theorem nb_ne2 (k : Fin 2) : (nbOf L g k).toNat ≠ 2 := by
  rw [nbOf_toNat]; split <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- **The class of an event**: an event of the state's shape that is neither undefined behaviour
nor a failed poll belongs to the class of its site, and to no other. -/
theorem ev_cls {d : D} {e : Event} (hev : Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hok : d.site.isPoll = true → ∀ m par a sc, e.kind ≠ .wait m par false a sc) (c : Cnt) :
    cls L g c e = decide (sig d.site = some c) := by
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hub hok
  cases s with
  | arr a | farr a =>
    fin_cases a <;> simp only [Ev, arrOff] at hev <;> subst hev <;>
      cases c <;> simp [cls, sig, bl_inj]
  | rarr a b | fdone a b =>
    fin_cases a <;> fin_cases b <;> simp only [Ev, arrOff] at hev <;>
      subst hev <;> cases c <;> simp [cls, sig, bl_inj]
  | free | farr0 =>
    simp only [Ev, arrOff] at hev; subst hev; cases c <;> simp [cls, sig, bl_inj]
  | fw a b =>
    fin_cases a <;> fin_cases b <;> simp only [Ev, pollOff, pollPar] at hev <;>
      obtain ⟨ok, rfl⟩ := hev <;> cases ok <;>
      first
      | exact absurd rfl (hok rfl _ _ _ _)
      | (cases c <;> simp [cls, sig, bl_inj])
  | wend l =>
    simp only [Ev, pollOff, pollPar] at hev; obtain ⟨ok, rfl⟩ := hev; cases ok <;>
      first
      | exact absurd rfl (hok rfl _ _ _ _)
      | (cases c <;> simp [cls, sig, bl_inj])
  | nb a | rbar a | fbar a =>
    simp only [Ev, barK] at hev; subst hev; rw [nbW_eq]
    cases c <;> simp [cls, sig, nb_inj, nb_ne2]
  | bar1 =>
    simp only [Ev] at hev; subst hev
    (cases c <;> simp [cls, sig]); exact fun h => nb_ne2 _ h.symm
  | barEnd l =>
    simp only [Ev] at hev
    rcases hev with rfl | ⟨f, rfl⟩
    · (cases c <;> simp [cls, sig]); exact fun h => nb_ne2 _ h.symm
    · exact absurd rfl (hub f)
  | fst a b c' | lse a =>
    simp only [Ev] at hev
    rcases hev with ⟨_, _, rfl⟩ | ⟨f, rfl⟩
    · cases c <;> simp [cls, sig]
    · exact absurd rfl (hub f)
  | word sk | down sk | up sk _ | total sk =>
    cases sk <;> simp only [Ev, rdOrUb, Epilogue.Ev, Site.toE] at hev <;>
      (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | (cases c <;> simp [cls, sig])
  | vote l | pre l | tiles l =>
    cases l <;> simp only [Ev, Epilogue.Ev, Site.toE] at hev <;>
      (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | (cases c <;> simp [cls, sig])
  | _ =>
    simp only [Ev, rdOrUb] at hev
    (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | (cases c <;> simp [cls, sig])

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
