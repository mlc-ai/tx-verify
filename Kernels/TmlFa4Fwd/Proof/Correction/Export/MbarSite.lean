-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Ledger
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Lemmas.Kernel.Safety.Classes
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' sites that name an mbarrier -/

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
/-- `corr_mbar` with the offsets of the sites that have a barrier. -/
theorem corr_mbar2 {d : Correction.D} {e : Event} {l : Loc} (hev : Correction.Ev p L g d e)
    (hm : MbarOf e l) :
    (e.kind = .arrive l 0 1 true .cta ∧ l = Correction.bl L g (Correction.arrOff d.site) ∧
        Correction.arrOff d.site ∈ [96, 104, 192, 200, 208, 216]) ∨
      ∃ par ok, e.kind = .wait l par ok true .cta ∧
        l = Correction.bl L g (Correction.pollOff d.site) ∧
        Correction.pollOff d.site ∈ [144, 224, 152, 232] := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp only [Correction.Ev] at hev
  all_goals first
    | (exfalso; rcases epi_site hev hm with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;>
        simp_all [Correction.Site.toE]; done)
    | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp only [MbarOf] at hm
  all_goals (try (rename_i a b; fin_cases a <;> fin_cases b))
  all_goals (try (rename_i a; fin_cases a))
  all_goals simp_all [Correction.rdOrUb, Correction.arrOff, Correction.pollOff]

set_option maxHeartbeats 8000000 in
/-- A correction lane's poll is at a poll site, with the site's parity. -/
theorem corr_poll_par {d : Correction.D} {e : Event} {l : Loc} {par : Nat} {ok acq : Bool}
    {sc : MbarScope} (hev : Correction.Ev p L g d e) (hk : e.kind = .wait l par ok acq sc) :
    par = Correction.pollPar d.site ∧
      ((∃ st j, d.site = .fw st j) ∨ ∃ b, d.site = .wend b) := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  have hm : MbarOf ⟨pc, .wait l par ok acq sc⟩ l := rfl
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp only [Correction.Ev] at hev
  case fw st j =>
    obtain ⟨ok', h⟩ := hev
    simp only [Kind.wait.injEq] at h
    exact ⟨h.2.1, .inl ⟨st, j, rfl⟩⟩
  case wend b =>
    obtain ⟨ok', h⟩ := hev
    simp only [Kind.wait.injEq] at h
    exact ⟨h.2.1, .inr ⟨b, rfl⟩⟩
  case down | up | total | pre | tiles =>
    exfalso
    rcases epi_site hev hm with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;> simp [Correction.Site.toE] at h
  all_goals exfalso
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Correction.rdOrUb]

set_option maxHeartbeats 8000000 in
/-- The named-barrier event of a correction lane, by its site. -/
theorem corr_bar_site {d : Correction.D} {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (hev : Correction.Ev p L g d ⟨pc, .bar id cnt mode⟩) :
    ((d.site = .bar1 ∧ mode = .sync ∨ (∃ l, d.site = .barEnd l) ∧ mode = .arrive) ∧ id = 2 ∧
        cnt = some 416) ∨
      ∃ s : Fin 2, (d.site = .nb s ∨ d.site = .rbar s ∨ d.site = .fbar s) ∧
        id = (Correction.nbOf L g s).toNat ∧ cnt = some 64 ∧ mode = .sync := by
  have hnb : ∀ s : Fin 2, Correction.nbW L g s = Correction.nbOf L g s := by
    intro s; fin_cases s <;> rfl
  obtain ⟨s, v, kk⟩ := d
  cases s <;> simp only [Correction.Ev] at hev
  case down | up | total | pre | tiles =>
    exfalso
    simp only [Epilogue.Ev, Correction.Site.toE] at hev
    (try split at hev)
    all_goals shape_destruct hev
    all_goals simp_all
  case bar1 => cases hev; simp
  case barEnd => rcases hev with h | ⟨_, h⟩ <;> cases h; simp
  case nb s => cases hev; exact .inr ⟨s, .inl rfl, by rw [← hnb]; rfl, rfl, rfl⟩
  case rbar s => cases hev; exact .inr ⟨s, .inr (.inl rfl), by rw [← hnb]; rfl, rfl, rfl⟩
  case fbar s => cases hev; exact .inr ⟨s, .inr (.inr rfl), by rw [← hnb]; rfl, rfl, rfl⟩
  all_goals exfalso
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Correction.rdOrUb]

end
end PTX.Kernels.TmlFa4Fwd.Proof
