-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Election
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexShuffle
import Lemmas.Step.WarpShfl

public section

/-! # Issuing the index warp's butterfly shuffles -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- Lanes at the same index butterfly can append one full-warp shuffle with actual operands. -/
theorem index_shuffle_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {extra second : Bool} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) (hub : ¬ HasUb X)
    (hall : ∀ h, SameWarp L g h → ∃ d, Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
      Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some (.index d)) ∧
      d.site = (if second then .quad2 extra else .quad1 extra)) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  let site : Wg1Index.Site := if second then .quad2 extra else .quad1 extra
  let word (h b : Nat) := b32 (if second then Wg1Index.pairWord P L h b (laneOf L h)
    else Wg1Index.laneWord P L h b (laneOf L h))
  let a (h : Nat) := if hw : SameWarp L g h then word h (hall h hw).choose.block else b32 0
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  refine PTX.Step.shfl_counted_extension_with_assumptions (pc := site.pc) (m := .bfly) hX hb
    a (fun _ => if second then 2 else 1) (fun _ => 31) hg ?_
    (fun h hw => (hall h hw).choose_spec.2.1) ?_ ?_
  · intro h hw
    obtain ⟨d, _, _, hState, _⟩ := hall h hw
    refine .inl ?_
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hState
    cases hState
  · intro h hw recv ok
    obtain ⟨hp, _, hState, hSite⟩ := (hall h hw).choose_spec
    obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
    obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
    obtain ⟨k, hTemplate⟩ := Wg1Index.quad_template hpre hSite ha hc
    rw [hTemplate] at hout
    have hp : u.pc = site.pc := ha.1.trans (congrArg Wg1Index.Site.pc hSite)
    dsimp only [a]
    rw [dite_eq_left hw]
    exact ⟨t, u, some (k recv ok), hRun, hTau, _, hout, recv, ok, by rw [hp], rfl⟩
  · apply all_wf_collective_batch hX (PTX.Step.warpThreads L g)
    · intro _ _ _ h
      exact Kind.noConfusion h
    · intro _ _ _ h
      exact Kind.noConfusion h
    · intro _ h
      exact Kind.noConfusion h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
