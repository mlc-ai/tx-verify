-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # An MMA lane's P-full polls at its exit

At its exit an MMA lane has polled a stage's P-full barrier for each of its commits to the stage's
S-full barrier (`mma_exit_polls`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
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
  obtain ⟨site, v⟩ := d
  cases site <;> simp only [Ev] at hev
  case exit l => exact ⟨l, rfl⟩
  all_goals exfalso
  all_goals (try simp only [Epilogue.Ev, Site.toE] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (simp only [reduceCtorEq] at *)

/-- **At its exit an MMA lane has polled a stage's P-full barrier for each of its S-full
commits.** -/
theorem mma_exit_polls (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 12) {k pc st : Nat}
    (hst : st < 2)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    Tm.sCommits L X g st k ≤ Tm.pPolls L X g st k := by
  rcases mma_counts hp hX hFw hw he (fun f h => by cases h) with ⟨s', n, hS, hev, hx⟩ | hev |
    ⟨d, n, r, w, hσ, hQ, hcm, hF, hev⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s'
    cases site
    case enter r => simp [exit] at hx
    case sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  · obtain ⟨l, hs⟩ := exit_site hev rfl
    have h1 : Tm.sCommits L X g st k = n (.mma (.commit (bl L g (80 + 8 * st)))) := by
      rw [← count hσ]; rfl
    have h2 : Tm.pPolls L X g st k = n (.mma (.acquire (bl L g (96 + 8 * st)))) := by
      rw [← count hσ, ← mma_okPolls]; rfl
    have hc := hQ.com (80 + 8 * st)
    have ha := hQ.acq (96 + 8 * st)
    change n _ = _ at hc ha
    rw [h1, h2, hc, ha, hs]
    have key : commitAt (Site.exit l).ord r (80 + 8 * st) =
        acqAt (Site.exit l).ord r (96 + 8 * st) := by
      interval_cases st <;> cases l <;> simp [Site.ord, commitAt, acqAt, pq] <;> omega
    rw [← key]
    split
    · exact le_rfl
    · exact Nat.zero_le _

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
