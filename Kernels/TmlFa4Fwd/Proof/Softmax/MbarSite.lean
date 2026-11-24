-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
public import Lemmas.Kernel.Safety.Classes
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' sites that name an mbarrier -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- The softmax warps name an object by an arrival at their stage's arrival offset or a poll at
its poll offset, both at a site that has a barrier. -/
theorem soft_mbar {d : Softmax.D} {e : Event} {l : Loc} (hev : Softmax.Ev p L g d e)
    (hm : MbarOf e l) :
    (e.kind = .arrive l 0 1 true .cta ∧ l = Softmax.bl L g (Softmax.arrOff d.site) ∧
        Softmax.arrOff d.site ∈ [336, 96, 112]) ∨
      ∃ par ok, e.kind = .wait l par ok true .cta ∧
        l = Softmax.bl L g (Softmax.pollOff d.site) ∧ Softmax.pollOff d.site ∈ [192, 80, 320] := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  all_goals first
    | (exfalso; rcases epi_site hev hm with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;>
        simp_all [Softmax.Site.toE]; done)
    | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp only [MbarOf] at hm
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb, Softmax.arrOff, Softmax.pollOff]

set_option maxHeartbeats 8000000 in
/-- A softmax lane's poll is at a poll site, with the site's parity word. -/
theorem soft_poll_par {d : Softmax.D} {e : Event} {l : Loc} {par : Nat} {ok acq : Bool}
    {sc : MbarScope} (hev : Softmax.Ev p L g d e) (hk : e.kind = .wait l par ok acq sc) :
    par = (truncBits 32 (Softmax.pollW d)).toNat % 2 ∧ d.site.isPoll = true := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  have hm : MbarOf ⟨pc, .wait l par ok acq sc⟩ l := rfl
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  case wq | ws | wb | pwend | wend =>
    obtain ⟨ok', h⟩ := hev
    simp only [Kind.wait.injEq] at h
    exact ⟨h.2.1, rfl⟩
  all_goals exfalso
  case down | up | total | pre | tiles =>
    rcases epi_site hev hm with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;> simp [Softmax.Site.toE] at h
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

set_option maxHeartbeats 8000000 in
/-- A softmax lane's election is at an election site. -/
theorem soft_elect_site {d : Softmax.D} {e : Event} {mask inst ld : Nat}
    (hev : Softmax.Ev p L g d e) (hk : e.kind = .elect mask inst ld) :
    ∃ r, d.site = .pel r ∧ e.pc = d.site.pc := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  case pel r =>
    rcases hev with ⟨_, _, h, -⟩ | ⟨_, h⟩
    · exact ⟨r, rfl, h⟩
    · cases h
  case down | up | total | pre | tiles =>
    exfalso
    simp only [Epilogue.Ev, Softmax.Site.toE] at hev
    (try split at hev)
    all_goals shape_destruct hev
    all_goals simp_all
  all_goals exfalso
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

set_option maxHeartbeats 8000000 in
/-- A softmax lane exits at the role's exit. -/
theorem soft_exit_site' {d : Softmax.D} {pc : Nat} (hev : Softmax.Ev p L g d ⟨pc, .exit⟩) :
    ∃ l, d.site = .exit l := by
  obtain ⟨s, v, kk, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  case exit l => exact ⟨l, rfl⟩
  case down | up | total | pre | tiles =>
    exfalso
    simp only [Epilogue.Ev, Softmax.Site.toE] at hev
    (try split at hev)
    all_goals shape_destruct hev
    all_goals simp_all
  all_goals exfalso
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

/-- The named-barrier event of a softmax lane, by its site. -/
theorem soft_bar_site {d : Softmax.D} {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (hev : Softmax.Ev p L g d ⟨pc, .bar id cnt mode⟩) :
    ((d.site = .bar1 ∧ mode = .sync ∨ (∃ l, d.site = .barEnd l) ∧ mode = .arrive) ∧ id = 2 ∧
        cnt = some 416) ∨
      ((∃ b, d.site = .bsync b) ∧ id = (if Softmax.stg L g then 12 else 11) ∧ cnt = some 128 ∧
        mode = .sync) ∨
      ((d.site = .finarr ∨ ∃ r, d.site = .narr r) ∧ id = (Softmax.nbW L g).toNat ∧
        cnt = some 64 ∧ mode = .arrive) := by
  obtain ⟨s, v, kk, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  case down | up | total | pre | tiles =>
    exfalso
    simp only [Epilogue.Ev, Softmax.Site.toE] at hev
    (try split at hev)
    all_goals shape_destruct hev
    all_goals simp_all
  case bar1 => cases hev; simp
  case barEnd => rcases hev with h | ⟨_, h⟩ <;> cases h; simp
  case bsync => cases hev; simp
  case narr => cases hev; simp
  case finarr => cases hev; simp
  all_goals exfalso
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

end
end PTX.Kernels.TmlFa4Fwd.Proof
