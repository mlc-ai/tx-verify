-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ElectOnce
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderTasks
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcQuery

@[expose] public section

/-! # An elected scheduler in its exit stage has polled its response barrier

A scheduler in its exit stage left its task loop after a query of a response that names no first
CTA,
or after an election whose leader is not its lane (`ExitQ`). A thread has one election event
(`elect_once_thm`), so a scheduler that is elected, with its election naming its own lane, left
after a
query. A query reports a response read right after a successful poll of the response barrier
(`clc_query`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An elected warp-10 thread in its scheduler's exit stage has polled its response barrier.** -/
theorem sched_elected_exit_thm (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g : Nat} {sd : Scheduler.D} (hg : g < L.threads)
    (hel : ∃ j pc mask inst, X.Elect (g, j) pc mask inst (laneOf L g))
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.sched sd))))
    (hx : Scheduler.exitOff sd ≠ none) :
    0 < okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
  have hsite : sd.site = .exitArrive ∨ sd.site = .exitWait ∨ sd.site = .exit := by
    obtain ⟨site, ap, cp, r, x⟩ := sd
    cases site <;> simp_all [Scheduler.exitOff]
  have hq := (Scheduler.run_of hpre hX hg hσ).exitQ
  rw [List.take_length] at hq
  rcases hq.1 hsite with ⟨i, e, hi, q, r, hk, -⟩ | ⟨i, e, hi, x, y, leader, hk, hne⟩
  · have he : X.get (g, i) = some e := hi
    rcases (Frame.trace (fun _ => sound hpre) hX hg).fired he with ⟨σ, -, hσi, -⟩ | ⟨-, pc', f, hf⟩
    · cases σ with
      | none => exact absurd hσi (tracked hpre hX g i hg)
      | some d =>
        obtain ⟨r', rfl⟩ := query_role hpre hX hg he hσi hk
        obtain ⟨j, pc, p, acq, sc, -, -, -, -, -, hw, -⟩ := clc_query hpre hX hg he hσi hk
        exact List.countP_pos_iff.mpr ⟨_, List.mem_of_getElem? hw,
          by simp [okPoll, sourceWaitSuccess]⟩
    · rw [hf] at hk
      cases hk
  · obtain ⟨j, pc, mask, inst, hj⟩ := hel
    obtain ⟨pce, ke⟩ := e
    simp only at hk
    subst hk
    have hij := elect_once_thm hpre hX hg (show X.Elect (g, i) pce x y leader from hi) hj
    subst hij
    have := (Option.some.inj ((show X.get (g, i) = _ from hi).symm.trans hj))
    simp only [Event.mk.injEq, Kind.elect.injEq] at this
    exact absurd this.2.2.2 hne

end
end PTX.Kernels.Fp16Gemm8192.Proof
