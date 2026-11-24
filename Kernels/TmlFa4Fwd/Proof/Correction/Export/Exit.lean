-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A correction lane's final O polls at its exit

A correction lane of a CTA with a tile has polled each stage's final O barrier at its exit
(`corr_exit_poll`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- An exit is fired at an exit site. -/
private theorem exit_site {d : D} {e : Event} (hev : Ev p L g d e) (hk : e.kind = .exit) :
    ∃ l, d.site = .exit l := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  obtain ⟨site, v, kk⟩ := d
  cases site <;> simp only [Ev] at hev
  case exit l => exact ⟨l, rfl⟩
  all_goals exfalso
  all_goals (try simp only [Epilogue.Ev, Site.toE] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [rdOrUb]

private theorem exit_tab : ∀ st : Fin 2,
    (ptsOf (.acquire (144 + 8 * st.val))).countP (before (.exit true)) = 1 ∧
      (ptsOf (.acquire (144 + 8 * st.val))).countP inRound = 0 := by
  decide

/-- **At its exit a correction lane of a CTA with a tile has polled each stage's final O barrier.**
-/
theorem corr_exit_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k pc : Nat} (st : Fin 2) (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (hP : ∃ R bal, Epilogue.Picked p L g R bal) :
    okPolls (obj L g (144 + 8 * st.val)) ((X.tr g).take k) = 1 := by
  rcases corr_counts_nonvote hp hX hFw hw hw1 he (fun f h => by cases h) (fun _ _ => nofun) with
    ⟨s', hev, hx⟩ | ⟨d, c, r, ℓ, _, _, hQ, hF, hev, hc⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s'
    cases site
    case enter r => simp [Proof.exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · obtain ⟨l, hs⟩ := exit_site hev rfl
    cases l
    · exfalso
      obtain ⟨rv, -, -, hFE, -⟩ := hF
      exact noPicked_of_exit hFE (by simp only [CorrWarp.toE, hs, CorrWarp.epi]) hP
    · have h1 := hQ.cnt (.acquire (144 + 8 * st.val)) (by simp)
      obtain ⟨t1, t2⟩ := exit_tab st
      rw [corr_okPolls, hc, h1, hs]
      simp only [passed, t1, t2, Nat.mul_zero, Nat.add_zero]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
