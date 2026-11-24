-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.MmaOperandSources
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.SoftmaxQkBlocker
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryCopy
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources

public section

/-! # Completion of already issued Tensor Core work in a maximal prefix -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A pending arithmetic operation can complete its operands and arithmetic, starting at the
earliest incomplete operation on its issuer's thread. -/
theorem mma_completion_extension (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hsg : SyncGuarded L kernel X)
    {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d s acc mask) (hn : X.async.mmaDone i = false) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  exact pending_mma_tmemA_of_byte_sources
    (fun _ _ _ _ hle => Interface.all_wf_effects hX hle rfl rfl rfl)
    (fun _ => tc_completion_extension hX) hX hsg (mma_operand_sources hpre hX hs ht)
    (mma_tmem_a_apart hpre hX hs ht) (mma_layout_injective hpre hX hs ht) hi hn

variable (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hmax hs ht

/-- Every issued Tensor Core copy or MMA has finished in a maximal tracked prefix. -/
theorem issued_tc_completed (hsg : SyncGuarded L kernel X) {i : EvId} (hi : X.TcAsync i) :
    X.async.mmaDone i = true := by
  cases hn : X.async.mmaDone i
  · exfalso
    apply hmax.not_grows
    rcases hi with ⟨d, s, acc, mask, hi⟩ | ⟨c, hi⟩ | ⟨s, hi⟩
    · exact mma_completion_extension hpre hmax.1 hs ht hsg hi hn
    · obtain ⟨g, i⟩ := i
      obtain ⟨chunk, rfl⟩ := MmaAccessWindow.copy_spec hpre hmax.1 hs ht hi
      cases ho : X.async.mmaOperands (g, i) with
      | none => exact query_copy_pending_extension hpre hmax.1 hs ht hi ho hn hsg
      | some ops =>
        apply tc_completion_extension hmax.1
          (by simp only [Snapshot.mmaStarted, ho, Option.isSome_some]) hn
        intro op hop
        obtain ⟨_, _, _, ⟨_, _, _, _, _, _, _, _, _, hm, _⟩, _⟩ :=
          TcMma.completionPrecedes_iff.mp hop
        have hKind := congrArg Event.kind (Option.some.inj (hi.choose_spec.symm.trans
          hm.choose_spec))
        cases hKind
    · obtain ⟨g, i⟩ := i
      exact (Wg0ScoreSources.no_shift_issue hpre hmax.1 hs ht hi).elim
  · rfl

/-- A maximal execution blocked on QK completion has an earlier pending MMA producer. -/
theorem pending_softmax_qk_earlier (hsg : SyncGuarded L kernel X) {g : Nat} {d : Wg0.D}
    (hp : PendingState P L X g (.wg0 d)) (hRel : PTX.Step.Released L X g) (hd : d.site = .qkDone) :
    ∃ h q, SameCta L g h ∧ PendingState P L X h q ∧
      priority P L h q < priority P L g (.wg0 d) := by
  rcases pending_softmax_qk_blocker hpre hmax hs ht hp hRel hd with h | ⟨_, _, _, _, _, hTrack, hn⟩
  · exact h
  · rw [issued_tc_completed hpre hmax hs ht hsg hTrack.2.2.1] at hn
    cases hn

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
