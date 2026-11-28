-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Common.Successor
import Kernels.InklingRelDecode.Proof.Mma.Commit
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs

/-! # The notification after the last PV step

The event after the last PV step of an iteration, if it is observed and not a fault, is the
empty-slot commit of that iteration's ordinal. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Frame

private theorem pv_seven (s : Site) (h : s.pc = Lib.pvIssue 7) : s = .pv 7 := by
  cases s <;> first | exact absurd h (by decide) | (rename_i j; fin_cases j <;>
    first | rfl | exact absurd h (by decide))

/-- **The empty commit follows the last PV step**. -/
public theorem pv_commit_next {Q L m X g k pc dst s acc mask ev} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩) (h7 : pc = Lib.pvIssue 7)
    (hn : X.get (g,k+1) = some ev) (hu : ∀ f, ev.kind ≠ .ub f) :
    ∃ sp, ev = ⟨2546,.tc (.commit sp)⟩ ∧
      pollRound 2510 ((X.tr g).take (k+1)) = pollRound 2510 ((X.tr g).take k) := by
  subst h7
  have hg := Frame.lt_of_get hX he
  have nuk (f : Fault) : (⟨Lib.pvIssue 7,.tc (.mma dst s acc mask)⟩ : Event).kind ≠ .ub f := nofun
  obtain ⟨w,x,r,⟨st,i,v⟩,n,hs,pcs⟩ := mma_state hp hX hf he nuk
    (by change 2422 < Lib.pvIssue 7; decide) (by change Lib.pvIssue 7 < 2557; decide)
  obtain rfl := pv_seven st pcs.symm
  obtain ⟨d',hd,keep⟩ := mma_successor hp hX hf hs he hn hu
  simp only [Mma.next, Mma.issueNext] at hd
  obtain rfl := Option.some.inj (Option.some.inj hd)
  have hs' := keep (by simp)
  obtain ⟨t,ins,o,hat,-,hc,ff⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX hn hs' hu
  have kind := commit_shape (regs := dispatchRegs Q L g w x) (w := w) hp hg .empty hat hc ff
  have pc' := Frame.event_pcU (fun g hg => thread_sound hp hg) hX hn hs' hu
  obtain ⟨epc,ek⟩ := ev
  change epc = 2546 at pc'
  change ek = _ at kind
  subst pc' kind
  refine ⟨_,rfl,?_⟩
  rw [List.take_add_one, show (X.tr g)[k]? = _ from he]
  simp [pollRound, okPollAt]

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
