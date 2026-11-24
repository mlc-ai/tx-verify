-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Control.SchedulerSucc
import Lemmas.Flow.ProjectU

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Proof PTX.Flow

private theorem sched_values {p L g} {d : Correction.D} (h : schedulerSite d.site = true) :
    values p L g (erase d) = Correction.values p L g d := by
  obtain ⟨s,v,k⟩ := d
  cases s with
  | setmax | bar1 | arr | word | down | up | total | q0 | q1 | uk | nb | free => rfl
  | vote l | pre l | tiles l | wend l | barEnd l | exit l => cases l <;> rfl
  | _ => cases h

private theorem sched_facts {p L g} {d : Correction.D} (h : schedulerSite d.site = true) :
    (code p L g).facts (erase d) = (Data.code p L g).facts d := by
  change factsFrom (liveAt d.site) _ = factsFrom _ _
  unfold liveAt
  simp only [h, ↓reduceIte]
  congr 1
  funext r
  unfold valueOf Correction.valueOf
  rw [sched_values h]

theorem scheduler_atD {p L g} {d : D} {t} (hs : schedulerSite d.site = true)
    (hat : (code p L g).AtD d t) : (Data.code p L g).AtD d.scheduler t := by
  have hf := sched_facts (p := p) (L := L) (g := g) (d := d.scheduler) hs
  obtain ⟨pc, sub, acc, fault, regs⟩ := hat
  exact ⟨pc, sub, acc, fault, hf ▸ regs⟩

/-- The full scheduler and request-selection proofs transfer, including every shuffle and
the late pass after the LSE. The final named barrier enters the rescale region separately. -/
theorem project_scheduler {p L g} (d : D)
    (strict : (Data.code p L g).StepAt d.scheduler) (hs : schedulerSite d.site = true)
    (hx : d.site ≠ .nb 1) :
    (code p L g).StepAtU d := by
  have hf : (code p L g).facts d = (Data.code p L g).facts d.scheduler :=
    sched_facts (d := d.scheduler) hs
  refine strict.projectU erase rfl hf rfl rfl id ?_ ?_
  · intro e
    obtain ⟨s,v,k⟩ := d
    cases s with
    | setmax | bar1 | arr | word | down | up | total | vote | pre | tiles | q0 | q1
    | uk | nb | free | wend | barEnd | exit => rfl
    | _ => cases hs
  · intro e d' t he hgood
    have hf' := sched_facts (p := p) (L := L) (g := g) (scheduler_succ (d := d.scheduler) hs hx he)
    obtain ⟨hat, hi⟩ := hgood
    obtain ⟨hpcAt, hsubAt, haccAt, hfaultAt, hregsAt⟩ := hat
    exact ⟨⟨hpcAt, hsubAt, haccAt, hfaultAt, hf' ▸ hregsAt⟩, hi⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
