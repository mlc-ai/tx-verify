-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Lemmas.Order.GuardSnoc
import Lemmas.Step.Issue

public section

/-! # Issuing the softmax output tiles -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- The pending softmax tile issue starts the actual asynchronous output store. -/
theorem softmax_output_issue_out {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} {j : Fin 4} {t : TState} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hg : g < L.threads) (hr : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : d.site = .tmaStore j) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u ∧
      out kernel Assumptions.all L g u =
        .ev (.tensorStore (P.param1Base + 512) (Wg0.outputSpec P L g j) (PTX.next u)) := by
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hg hr hσ
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (Wg0.outputTma_code j))
  have hInv : Wg0.Inv P L g d := hi
  rw [Wg0.outputTma_known hpre ha hd hInv.warpLt (Wg1Mma.queryOf_lt hpre hg)
    (Wg1Mma.eOf_lt_b hpre)] at hout
  exact ⟨u, hTau, hout⟩

/-- Issuing the pending output tile extends the execution. Its effects are separate steps. -/
theorem softmax_output_issue_extension
    {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} {j : Fin 4} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hsg : SyncGuarded L kernel X)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a old new, X.get e = some ⟨pc, .rmw a old new⟩ → a.release = false)
    (hnf : ∀ e sem scope, ¬ X.ThreadFence e sem scope)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : d.site = .tmaStore j) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, hTau, hout⟩ := softmax_output_issue_out hpre hs hp.1 hRun hσ hd
  let ev : Event := ⟨u.pc, .tensorStore (P.param1Base + 512) (Wg0.outputSpec P L g j)⟩
  have hStep : EStep kernel Assumptions.all L g u ev (some (PTX.next u)) :=
    ⟨_, hout, rfl, rfl⟩
  refine PTX.Step.issue_counted_extension_reads hX hord hp.1 hne hrel hRun hTau hStep
    (.inr (.inl ⟨_, _, rfl⟩)) (Interface.all_wf_snoc_of_not_nc hX nofun nofun) ?_
  exact hsg.snoc hnr hnrmw hnf (ev := ev) nofun nofun nofun (by intros; simp_all [ev])

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
