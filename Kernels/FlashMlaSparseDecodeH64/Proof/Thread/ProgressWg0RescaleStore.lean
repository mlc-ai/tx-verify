-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
import Lemmas.Step.TcLoad

public section

/-! # The softmax accumulator rescale store -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- A released softmax lane can store the converted words of its accumulator group. -/
theorem softmax_rescale_store_extension {P : Params} {L : Launch} {mem0 : Mem0}
    {X : Execution} {g : Nat} {d : Wg0.D} {j : Fin 4} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : d.site = .rescaleStore j) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hσ
  rw [Wg0.rescaleStore_template hpre hd ha hc] at hout
  let ev : Event := ⟨u.pc, .tc (.st (64 * j.val) (Wg0.rescaleStoreValues d) .s32x32b)⟩
  have hEvent : EStep kernel Assumptions.all L g u ev (some (PTX.next u)) :=
    ⟨_, hout, rfl, rfl⟩
  exact PTX.Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hRun hTau hEvent rfl
    (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc nofun)
    (Interface.all_wf_snoc_of_not_nc hX nofun nofun)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
