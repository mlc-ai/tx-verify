-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.Softmax.Ref
public import Kernels.TmlFa4Fwd.Proof.Softmax.RefSucc
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The ledger classes of the softmax warps' events

An event of the shape table at a state (`Ev`) that is no undefined behaviour, no failed poll,
not the implicit wait of a delayed P store and, at a plain load's implicit wait, at sub-step 1,
belongs to the class `sig` of its site among the pointed classes and the elected lane's arrival
(`ev_cls`): arrivals and polls name their barrier by its shared offset, the CTA barriers are
barrier 2, the warp group's named barrier `nbW` (3 to 10) or the stage's (11 or 12), and the
stores are the statistics and final stores. The won elections are counted at the election only
(`ev_won`, `ev_won_pel`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem bl_inj {a b : Nat} : bl L g a = bl L g b ↔ a = b := by
  simp [bl]

/-- The warp group's named barrier is 3 to 10. -/
theorem nbW_range (hp : Pre p L m) : 3 ≤ (nbW L g).toNat ∧ (nbW L g).toNat ≤ 10 := by
  have hb := hp.block
  simp only [nbW, stg, warpW]
  have hw : g % L.block / 32 < 16 := by rw [hb]; omega
  generalize g % L.block / 32 = w at hw ⊢
  interval_cases w <;> decide

theorem nbW_ne2 (hp : Pre p L m) : (nbW L g).toNat ≠ 2 := by
  have := nbW_range (g := g) hp; omega

theorem nbW_ne_sb (hp : Pre p L m) (c : Bool) : (nbW L g).toNat ≠ if c then 12 else 11 := by
  have := nbW_range (g := g) hp; cases c <;> simp <;> omega

/-- The classes `ev_cls` speaks of: the pointed ones and the elected lane's arrival. -/
def Cnt.sited (c : Cnt) : Bool := c.pointed || c == .arrive 112

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- **The class of an event**: an event of the state's shape that is neither undefined behaviour
nor a failed poll nor the implicit wait of a delayed P store, at a plain load's implicit wait at
sub-step 1, belongs to the class of its site among the sited classes. -/
theorem ev_cls (hp : Pre p L m) {d : D} {e : Event} (hev : Ev p L g d e)
    (hub : ∀ f, e.kind ≠ .ub f)
    (hok : d.site.isPoll = true → ∀ m par a sc, e.kind ≠ .wait m par false a sc)
    (hdel : d.site.delayed = true → d.k ≠ 0) (hw : ∀ c, d.site = .sldw c → d.k = 1)
    {c : Cnt} (hc : c.sited = true) :
    cls L g c e = decide (sig d.site = some c) := by
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hub hok hdel hw
  have hr := nbW_range (g := g) hp
  cases s with
  | barr _ | parr _ | parr2 _ =>
    simp only [Ev, arrOff] at hev; subst hev
    cases c <;> simp_all [cls, sig, bl_inj, Cnt.pointed, Cnt.sited]
  | wq | ws _ | wb _ | pwend _ | wend _ =>
    simp only [Ev, pollOff] at hev; obtain ⟨ok, rfl⟩ := hev; cases ok
    · exact absurd rfl (hok rfl _ _ _ _)
    · cases c <;> simp_all [cls, sig, bl_inj, Cnt.pointed, Cnt.sited]
  | bar1 | bsync _ | narr _ | finarr =>
    simp only [Ev] at hev; subst hev
    cases c <;> first
      | (simp_all [cls, sig, Cnt.pointed, Cnt.sited]; done)
      | (simp_all [cls, sig, Cnt.pointed, Cnt.sited]; omega)
      | (simp_all [cls, sig, Cnt.pointed, Cnt.sited]; split <;> omega)
  | barEnd _ =>
    simp only [Ev] at hev
    rcases hev with rfl | ⟨f, rfl⟩
    · cases c <;> first
        | (simp_all [cls, sig, Cnt.pointed, Cnt.sited]; done)
        | (simp_all [cls, sig, Cnt.pointed, Cnt.sited]; omega)
        | (simp_all [cls, sig, Cnt.pointed, Cnt.sited]; split <;> omega)
    · exact absurd rfl (hub f)
  | sldw _ =>
    simp only [Ev] at hev
    split at hev
    · rcases hev with rfl | ⟨f, rfl⟩
      · cases c <;> simp_all [cls, sig]
      · exact absurd rfl (hub f)
    · rename_i h; simp [hw _ rfl] at h
  | pst r q =>
    simp only [Ev] at hev
    split at hev
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact absurd (Fin.ext h.2) (hdel h.1)
    · rcases hev with ⟨_, _, _, rfl⟩ | ⟨f, rfl⟩
      · cases c <;> simp_all [cls, sig]
      · exact absurd rfl (hub f)
  | word sk | down sk | up sk _ | total sk =>
    cases sk <;> simp only [Ev, rdOrUb, Epilogue.Ev, Site.toE] at hev <;>
      (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | (cases c <;> simp_all [cls, sig, Cnt.pointed, Cnt.sited])
  | vote l | pre l | tiles l =>
    cases l <;> simp only [Ev, Epilogue.Ev, Site.toE] at hev <;>
      (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | (cases c <;> simp_all [cls, sig, Cnt.pointed, Cnt.sited])
  | _ =>
    simp only [Ev, rdOrUb, tcLdOrUb] at hev
    (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | (cases c <;> simp_all [cls, sig, Cnt.pointed, Cnt.sited])

/-- At a site other than the election, no event of the state's shape is a won election. -/
theorem ev_won {d : D} {e : Event} (hev : Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpel : d.site.isPel = false) (pc : Nat) : cls L g (.won pc) e = false := by
  obtain ⟨s, v, k, acc⟩ := d
  obtain ⟨epc, kd⟩ := e
  simp only at hub
  cases s with
  | pel _ => simp [Site.isPel] at hpel
  | word sk | down sk | up sk _ | total sk =>
    cases sk <;> simp only [Ev, rdOrUb, Epilogue.Ev, Site.toE] at hev <;>
      (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | simp [cls]
  | vote l | pre l | tiles l =>
    cases l <;> simp only [Ev, Epilogue.Ev, Site.toE] at hev <;>
      (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | simp [cls]
  | pst r q =>
    simp only [Ev, tcLdOrUb] at hev
    split at hev <;>
      (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | simp [cls]
  | sldw q =>
    simp only [Ev, tcLdOrUb] at hev
    split at hev <;>
      (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | simp [cls]
  | _ =>
    simp only [Ev, rdOrUb, tcLdOrUb] at hev
    (try casesm* (∃ _, _), _ ∨ _) <;> subst_vars <;>
      first | exact absurd rfl (hub _) | simp [cls]

/-- At the election, the won election of its own program counter is counted when the lane is the
elected one. -/
theorem ev_won_pel {r : Rd} {v : V} {k : Fin 4} {acc : List Value} {e : Event}
    (hev : Ev p L g ⟨.pel r, v, k, acc⟩ e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ m inst ld, e.kind = .elect m inst ld ∧
      ∀ pc, cls L g (.won pc) e = (decide ((Site.pel r).pc = pc) && decide (ld = laneOf L g)) := by
  simp only [Ev] at hev
  rcases hev with ⟨inst, ld, hpc, hk⟩ | ⟨f, hk⟩
  · refine ⟨_, inst, ld, hk, fun pc => ?_⟩
    simp only [cls, hk, hpc]
  · exact absurd hk (hub f)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
