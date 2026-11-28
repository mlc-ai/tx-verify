-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollW0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0VoteSucc
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime

@[expose] public section

/-! # A lane of warps 0 to 3 at the vote is released

The vote is reached from the load of the row maxima (`Wg0.succ_vote`), whose event is a load: the
lane's last event never blocks. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- **A lane of warps 0 to 3 at the vote is released.** -/
theorem w0_vote_rel (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x < 4)
    {d : Wg0.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X x (X.tr x).length = some (some (w0S P L x d n)))
    (hs : d.site = .vote) : Step.Released L X x := by
  by_cases h0 : (X.tr x).length = 0
  · exact Sched.released_nil (List.length_eq_zero_iff.mp h0)
  have hlen : 0 < (X.tr x).length := Nat.pos_of_ne_zero h0
  obtain ⟨ey, hey⟩ : ∃ ey, (X.tr x)[(X.tr x).length - 1]? = some ey :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hst : Frame.stateAt (thread P L) X x ((X.tr x).length - 1 + 1) =
      some (some (w0S P L x d n)) := by
    rw [Nat.sub_add_cancel hlen]; exact hσ
  obtain ⟨σm, hσm, hnm⟩ := prev_state hey hst
  have heyget : X.get (x, (X.tr x).length - 1) = some ey := hey
  have hney : ∀ f, ey.kind ≠ .ub f := fun f hf => hub ⟨(x, (X.tr x).length - 1), ey.pc, f, by
    rw [heyget]; obtain ⟨pc, kd⟩ := ey; simp only at hf; rw [hf]⟩
  rcases w0_cls hFw hx hw hσm with ⟨dm, nm, rfl, hWm, -⟩ | ⟨dm, nm, rfl⟩
  · have := startup_to_w0 hp hw hWm hnm rfl
    rw [this] at hs
    cases hs
  · obtain ⟨d', hsu, hσeq⟩ := w0_next hnm
    simp only [w0S, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hσeq
    obtain ⟨rfl, -⟩ := hσeq
    have hmld := Wg0.succ_vote (batch_in hp x) hsu hs
    obtain ⟨σ0m, hσ0m, -, -, hevm⟩ := ev_state hp hX hFw heyget hney
    rw [hσm] at hσ0m
    obtain rfl := Option.some.inj (Option.some.inj hσ0m)
    obtain ⟨-, hKm⟩ : Wg0.Ev P L x (warpW L x) dm ey := hevm
    unfold Wg0.EvK at hKm
    rw [hmld] at hKm
    rcases hKm with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · exact Sched.released_of_unblocking heyget (by rw [hk]; trivial)
    · exact (hney f hk).elim

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
