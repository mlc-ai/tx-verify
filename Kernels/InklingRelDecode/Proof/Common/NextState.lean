-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.StartupEvents
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Kernel.Progress.NextEv
import all Kernels.InklingRelDecode.Proof.Common.Follow

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Sched

/-- Transfer the reference at the end of the current lane to its witnessing trace.
Only this lane prefix is required to agree. -/
theorem next_state {Q L m X g ev} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g ev) (hu : ∀ f, ev.kind≠.ub f) :
    ∃ s : (thread Q L g).D, stateAt (thread Q L) X g (X.tr g).length = some (some s) ∧
      tableInv Q L g s ∧ ev.pc=(thread Q L g).pc s ∧
      ∃ t ins o, (thread Q L g).AtD s t ∧ kernel.code[ev.pc]?=some ins ∧
        Fires ev.pc (eventTmpl Assumptions.all L g t ins.op) ev o := by
  have hg := hn.lt
  obtain ⟨Y,hY,pre,get⟩ := hn
  have eq := stateAt_congr (C := thread Q L) (by simpa using pre :
    (Y.tr g).take (X.tr g).length = (X.tr g).take (X.tr g).length)
  have prev := hf g hg (X.tr g).length
  change FollowedAt _ _ X g _ at prev
  unfold FollowedAt at prev
  rw [←eq] at prev
  obtain ⟨s,hs,_⟩ := good_stateU (fun g h => thread_sound hp h) hY get
    (fun _ f h => hu f (congrArg Event.kind h)) prev
  have pc := event_pcU (fun g h => thread_sound hp h) hY get hs hu
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := fired_siteU (fun g h => thread_sound hp h) hY get hs hu
  exact ⟨s,eq ▸ hs,prev.2 s hs (prefix_ub_zero hs (noUbBefore_of_get hY get)),
    pc,t,ins,o,ht,pc ▸ hc,pc ▸ fire⟩

end PTX.Kernels.InklingRelDecode.Proof
