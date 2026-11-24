-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Gen.StepCorrection
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Lemmas.Flow.BallotU
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl
import Kernels.TmlFa4Fwd.Proof.Correction.Havoc

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof

set_option maxRecDepth 100000

private theorem discard_keys {v : Nat → Value} {rs : List Nat} :
    (factsFrom rs v).map Prod.fst = rs := by
  simp only [factsFrom, List.map_map, Function.comp_def]
  exact List.map_id _

theorem bra_rule {L g target uni} (t : TState) (a : Assumption) (ha : a ∈ Assumptions.all) :
    a.localRule L g t (.bra target uni) = none := by
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option hygiene false in
local macro "ballot_at " st:term:max " via " lookup:term:max " branch " branch:term:max
    " at " pc:num " on " pred:num : tactic =>
  `(tactic| (
    refine Code.ballotU (C := code p L g)
      (dst := fun b => erase (afterVote $st ⟨.rvote $st,v.scheduler,0⟩ (BitVec.ofNat 64 b.toNat)))
      $lookup ?_ (fun _ _ => rfl) rfl rfl ?_ (fun _ => rfl) ?_ ?_
    · change _ ∉ (factsFrom _ _).map Prod.fst
      rw [discard_keys]
      dsimp only [live, D.site]
      decide +kernel
    · intro b
      dsimp only [afterVote, Correction.D.ite]
      split <;> rfl
    · intro b
      dsimp only [afterVote, Correction.D.ite]
      split <;> exact Or.inl rfl
    · intro b
      let q := Epilogue.scmpi .eq .b (BitVec.ofNat 64 b.toNat) 0
      refine SegU.comp (b := $pc) (G := (($pred,.pred q) :: facts p L g ⟨.rvote $st,v,0⟩)) ?_ ?_
      · dsimp only [code, facts]
        apply SegU.of_seg (n := 1)
        intro t ht
        seg_fp ht using rfl
      · refine SegU.comp (SegU.branch q $branch bra_rule (Epilogue.segFree (by decide))) ?_
        dsimp only [code, facts, afterVote, Correction.D.ite, erase]
        cases hq : q
        · simp only [show Epilogue.scmpi .eq .b (BitVec.ofNat 64 b.toNat) 0 = q from rfl,
            hq, Bool.false_eq_true, ↓reduceIte]
          seg_ctl rules_frame, hooks_ok
        · simp only [show Epilogue.scmpi .eq .b (BitVec.ofNat 64 b.toNat) 0 = q from rfl,
            hq, ↓reduceIte]
          seg_ctl rules_frame, hooks_ok))


theorem stepAt_rvoteU {p L g} (st : Fin 2) (v : V) :
    (code p L g).StepAtU ⟨.rvote st,v,0⟩ := by
  fin_cases st
  · ballot_at 0 via Flow.code_8009 branch Flow.code_8011 at 8011 on 732
  · ballot_at 1 via Flow.code_8228 branch Flow.code_8230 at 8230 on 734

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
