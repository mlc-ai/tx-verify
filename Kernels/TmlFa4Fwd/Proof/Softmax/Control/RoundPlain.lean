-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.RoundPlainTail
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.WaitU
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl
import Lemmas.Flow.SegJump

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc

set_option maxRecDepth 100000
set_option maxHeartbeats 900000

open PlainWait in
theorem stepAt_pwend_plainU (hp : Pre p L m) (v : V) :
    (code p L g).StepAtU ⟨.pwend .plain,v,0,[]⟩ := by
  refine Code.waitU (dst := fun ok => if ok then dest v else ⟨.pwend .plain,v,0,[]⟩)
    Flow.code_7463 ?_ ?_ rfl rfl (fun ok => by cases ok <;> rfl)
    (fun ok => by cases ok <;> rfl) ?_ ?_
  · change _ ∉ (factsFrom _ _).map Prod.fst
    rw [keys]
    dsimp only [D.scheduler,livePc]
    decide +kernel
  · intro m q ok s
    cases ok
    · rfl
    · exact advance v (e := ⟨7463,.wait m q true true s⟩) rfl
  · intro ok
    cases ok
    · exact .inl ⟨rfl,rfl,rfl⟩
    · cases h : cond v <;> simp only [dest,h,Bool.false_eq_true,↓reduceIte] <;>
        exact .inl ⟨rfl,rfl,rfl⟩
  · intro ok
    refine (SegU.branch ok Flow.code_7464 (fun t => braFree t.pc _ _ t rfl)
      (Epilogue.segFree (by decide))).comp ?_
    cases ok
    · exact SegU.of_seg (seg_jmp Flow.code_7465 (braFree _ _ _) (Epilogue.segFree (by decide)))
    · exact tail hp v

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
