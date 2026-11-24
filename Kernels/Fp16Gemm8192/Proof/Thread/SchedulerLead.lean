-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerCount

@[expose] public section

/-! # The leader's requests and their response arrivals

The leader CTA's scheduler requests a cancellation at `tryCancel`, right after a successful
acknowledgement poll, and then arrives on its own CLC response barrier expecting the response at
`arriveTx`. On the leader CTA the task loop enters `arriveTx` only from `tryCancel` (`loopHead`).
Along its run (`LeadRel`), its requests on that barrier exceed its response arrivals by one exactly
while it is at `arriveTx`, so each response arrival follows the request it expects
(`Scheduler.lead_arrive_after_issue`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- A leader scheduler's response arrival follows one more of its requests on that response
barrier than its earlier response arrivals: the request it expects is issued first. -/
theorem Scheduler.lead_arrive_after_issue (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) {k : Nat} {e : Event} {sd : Scheduler.D}
    {tx n : Nat} {rel : Bool} {sc : MbarScope} (hg : g < L.threads)
    (he : X.get (g, k) = some e)
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.sched sd))))
    (hl : Loader.leader L g = true)
    (hk : e.kind = .arrive (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) tx n rel sc) :
    arrivals (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take k) + 1 ≤
      ((X.tr g).take k).countP (clcIssuesTo (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)) := by
  change arrivals (clcResp L g) ((X.tr g).take k) + 1 ≤
    ((X.tr g).take k).countP (clcIssuesTo (clcResp L g))
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hL : Scheduler.LeadRel L g sd ((X.tr g).take k) := (Scheduler.run_of hpre hX hg hσ).lead
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hcount := hL hl
  rcases arrive_site hpre hg hat hc hfire hk with ⟨hs, -⟩ | ⟨-, hm⟩
  · simp only [hs, ↓reduceIte] at hcount
    omega
  · have := congrArg Loc.addr hm
    simp [leadAck, Bar.loc, Bar.off] at this

end
end PTX.Kernels.Fp16Gemm8192.Proof
