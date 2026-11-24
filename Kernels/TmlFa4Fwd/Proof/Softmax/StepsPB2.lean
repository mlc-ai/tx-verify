-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPB
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.Step.TcSteps

@[expose] public section

/-! # A bias round's P part: the stores' unpacks, the steps

As the first round's (`StepsP1.lean`): after the first P store (sub-step 1 of `pst .bias 0`), the
second (`pst .bias 1`) and the arrival between the store waits (`parr .bias`), eight unpacks of
packed words into the next store's halves (`Gen.pkBA_run`, `pkBB`, `pkBC`), whose condition holds
by the words' kind (the tail's end kinds per path, `pB_words`), the state's other facts carried,
landing on the next store's table (`pBData`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- An unpack run from state `d` between two states of the first round's P part, landing on the
second (`d'`). -/
macro "pB_unpack " d:term:max d':term:max run:ident eq:ident f0:ident items:ident
    hG:ident sp:ident : tactic =>
  `(tactic| (
  have hrun := $run L g (valueOfD p L g $d)
  have hfr := SegD.frame (H := factsD p L g $d) Gen.rulesFrame hrun rfl (by kernel_rfl)
    (by kernel_rfl) (Gen.segFree_range (by kernel_rfl))
  refine seg_of_segD (hfr.weaken_start ?_ |>.weaken_end ?_) ?_
  · intro R hR
    refine (holds_append _ _ _).mpr ⟨?_, hR⟩
    rw [$eq:ident]
    exact holds_sub hR (by kernel_rfl)
  · intro R hR
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    exact land_run (unpack_landB ($sp _) (pB_halves (d := $d) (d' := $d') rfl rfl rfl))
      (fun r _ => rfl) (by kernel_rfl) h1 h2
  · have hV : ∀ r, (kOf ((($f0 (valueOfD p L g $d)).map Prod.fst).map fun r => (r, Kd.pr .w4))
        r).Has (lookupD ($f0 (valueOfD p L g $d)) r) := by
      rw [$eq:ident]
      exact kstart (by kernel_rfl) (pB_words hp rfl (by kernel_rfl))
    exact (kpiece ($hG _) (by kernel_rfl) hV (by simp [kFns, XItem.FnOk, $items:ident])).1))

/-- **The first P store** after its implicit wait, and the unpacks of the second store's halves. -/
theorem stepAt_pstB_0s (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.pst .bias 0, v, 1, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_tcStStore (dn := D.mk' (.pst .bias 1) v) (by code_lookup)
    (by rw [Assumptions.all_tcStWaitLd]; kernel_rfl) rfl rfl (fun _ => rfl)
    ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  pB_unpack (⟨.pst .bias 0, v, 1, []⟩ : D) (D.mk' (.pst .bias 1) v) Gen.pkBA_run pkBA_facts0_eq
    Gen.pkBA_facts0 Gen.pkBA_items0 pkBA_G pkBA_spec

/-- **The second P store** and the unpacks of the third store's halves. -/
theorem stepAt_pstB_1 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.pst .bias 1, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_issueAt (dn := D.mk' (.pst .bias 2) v) (by code_lookup)
    (fun hpc hf => fires_tcSt_next (by rw [hpc, Assumptions.all_tcStWaitLd]; rfl) hf)
    (fun _ => rfl) rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  pB_unpack (⟨.pst .bias 1, v, 0, []⟩ : D) (D.mk' (.pst .bias 2) v) Gen.pkBB_run pkBB_facts0_eq
    Gen.pkBB_facts0 Gen.pkBB_items0 pkBB_G pkBB_spec

/-- **The arrival between the store waits** and the unpacks of the fourth store's halves. -/
theorem stepAt_parrB (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.parr .bias, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_arrive (dn := D.mk' (.pst .bias 3) v) (by code_lookup) ?_
    (fun _ => rfl) rfl rfl ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro r hr q hq e
    cases hr
    have hk : (liveD (livePc ⟨.parr .bias, v, 0, []⟩)).contains 8603 = false := by kernel_rfl
    simp only [factsD, factsFrom, List.mem_map] at hq
    obtain ⟨r', hr', rfl⟩ := hq
    simp only at e
    subst e
    rw [List.contains_iff_mem.mpr hr'] at hk
    cases hk
  · pB_unpack (⟨.parr .bias, v, 0, []⟩ : D) (D.mk' (.pst .bias 3) v) Gen.pkBC_run pkBC_facts0_eq
      Gen.pkBC_facts0 Gen.pkBC_items0 pkBC_G pkBC_spec

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
