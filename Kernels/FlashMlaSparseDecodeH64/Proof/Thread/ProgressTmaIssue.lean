-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbTmaGather
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaCoordinateRef
import Lemmas.Order.GuardSnoc
import Lemmas.Step.Issue

public section

/-! # Append the gather producer's actual TMA issue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- A released gather lane issues the actual four-row copy from its represented operands. -/
theorem tma_issue_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Tma.D} {k : Fin 16} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hSafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hp : Frame.Pending L X g) (hRel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.tma d)))
    (hd : d.site = .issue k) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX (fun hub => hSafe (.inl hub)) hp
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (Wg1Tma.issueInstr_code k))
  obtain ⟨addr, spec, hTmpl⟩ := UbTma.gather_template hpre hX.cluster.1 hp.1 hd ha hi
    (TmaCoordinateRef.issue_words hpre hX hs hSigma hd)
  rw [hTmpl] at hout
  let ev : Event := ⟨u.pc, .tensorIssue addr spec⟩
  have hStep : EStep kernel Assumptions.all L g u ev (some (PTX.next u)) :=
    ⟨_, hout, rfl, rfl⟩
  exact PTX.Step.issue_counted_extension_reads hX hord hp.1 hn hRel hRun hTau hStep
    (.inl ⟨_, _, rfl⟩)
    (Interface.all_wf_snoc_of_not_nc hX (fun _ _ h => Kind.noConfusion h)
      (fun h => Kind.noConfusion h))
    ((sync_guarded hX hSafe).snoc
      (fun _ _ _ _ he => write_no_release hX he)
      (fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim)
      (no_thread_fence hX)
      (ev := ev) (fun _ _ h => Kind.noConfusion h) (fun _ _ _ h => Kind.noConfusion h)
      (fun _ _ h => Kind.noConfusion h)
      (fun _ _ _ _ _ h => Kind.noConfusion (congrArg Event.kind h)))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
