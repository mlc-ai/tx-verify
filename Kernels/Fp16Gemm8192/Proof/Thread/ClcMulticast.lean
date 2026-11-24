-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RingUsers
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerSites
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked

@[expose] public section

/-! # The cancellation requests multicast to their whole cluster

The kernel's only cancellation request is a multicast request (`clcTryCancel true`, at the
scheduler's `tryCancel` site). Its targets are every CTA below the grid of its issuing CTA's cluster
(`clcTmpl`). So every such request names each CTA of its cluster: the converse of the bound that
`ring_event` gives for the targets. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A multicast cancellation request's targets are every CTA below the grid in the issuing CTA's
cluster. -/
theorem fires_clcIssue_all {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {dst mb : Nat} {doff moff : Int} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.clcTryCancel true dst doff mb moff)) e o) :
    ∀ sp targets, e.kind = .clcIssue sp targets →
      ∀ c, c < L.grid → L.clusterOfCta c = L.clusterOfCta (g / L.block) → c ∈ targets := by
  intro sp targets hk c hcg hcl
  simp only [eventTmpl, clcTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases hd : effAddr L g t .shared dst doff with
  | error f =>
    simp only [hd, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok d =>
    cases hm : mbarLoc L g t mb moff with
    | error f =>
      simp only [hd, hm, ofExec, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | ok m =>
      simp only [hd, hm] at hf
      split at hf
      · simp only [ofExec, Fires] at hf
        rw [hf.1] at hk
        cases hk
        simp [List.mem_filter, List.mem_range, hcg, hcl]
      · simp only [ofExec, Fires] at hf
        rw [hf.1] at hk
        cases hk

set_option maxHeartbeats 4000000 in
/-- **Every cancellation request of a thread names every CTA of its cluster below the grid.** The
request is the scheduler's (`ring_event`), at its `tryCancel` site (`Scheduler.clcIssue_site`),
whose
instruction is the kernel's multicast cancellation request. -/
theorem clc_multicast_thm {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ (h ki pc : Nat) (sp : Clc.Spec) (tg : List Nat),
      X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩ →
      ∀ c', c' < L.grid → c' / 2 = h / L.block / 2 → c' ∈ tg := by
  intro h ki pc sp tg hget c' hc' hcl
  have hh : h < L.threads := Frame.lt_of_get hX hget
  have hk : (⟨pc, .clcIssue sp tg⟩ : Event).kind = .clcIssue sp tg := rfl
  rcases (Frame.trace (fun _ => sound hpre) hX hh).fired hget with
    ⟨τ, -, hτ, -⟩ | ⟨-, hub⟩
  swap
  · obtain ⟨pc', f, hf'⟩ := hub
    cases hf'
  have hσ : Frame.stateAt (code L) X h ki = some τ := hτ
  cases τ with
  | none => exact absurd hσ (tracked hpre hX h ki hh)
  | some d =>
    have hR := ring_event hpre hX hh hget hσ
    obtain ⟨b, -, hb, -⟩ := hR.clc sp tg hk
    obtain ⟨k, i, f⟩ := b
    have hsd : ∃ sd, d = .inr (.sched sd) := by
      cases k <;> cases f <;> simp only [Bar.clcBy] at hb
      exact hb.1
    obtain ⟨sd, rfl⟩ := hsd
    obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX hget hσ
    obtain ⟨site, ap, cp, resp, x⟩ := sd
    have hs := Scheduler.clcIssue_site hat hc hfire hk
    simp only at hs
    subst hs
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clcIssue_0)
    have hfire' : Fires _ (eventTmpl Prod L h t (.clcTryCancel true 634 0 635 0))
        ⟨pc, .clcIssue sp tg⟩ o := hfire
    have hcl' : L.clusterOfCta c' = L.clusterOfCta (h / L.block) := by
      simpa [clusterOfCta_eq hpre] using hcl
    exact fires_clcIssue_all hfire' sp tg hk c' hc' hcl'

end
end PTX.Kernels.Fp16Gemm8192.Proof
