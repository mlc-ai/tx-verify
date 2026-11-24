-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part080
import Kernels.TmlFa4Fwd.Flow.Code.Part081
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.WaitU
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl
import Lemmas.Flow.SegJump

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc

set_option maxRecDepth 100000

private theorem keys {v : Nat → Value} {rs : List Nat} :
    (factsFrom rs v).map Prod.fst = rs := by
  simp only [factsFrom, List.map_map, Function.comp_def]
  exact List.map_id _

set_option hygiene false in
local macro "poll_at " s:term:max " to " doneSite:term:max " via " mem:term:max ","
    branch:term:max "," jump:term:max : tactic =>
  `(tactic| (
    refine Code.waitU (C := code p L g) (dst := fun ok => ⟨if ok then $doneSite else $s,v,0,[]⟩)
      $mem ?_ (fun m q ok s => by cases ok <;> rfl) rfl rfl (fun _ => rfl) (fun _ => rfl)
      (fun ok => by cases ok <;> first | exact .inl ⟨rfl,rfl,rfl⟩ | rfl) ?_
    · change _ ∉ (factsFrom _ _).map Prod.fst
      rw [keys]
      dsimp only [Softmax.facts, D.scheduler, livePc]
      decide +kernel
    · intro ok
      refine SegU.comp (SegU.branch (pc := Site.pc $s + 1) ok $branch
        (fun t => braFree t.pc _ _ t rfl)
        (Epilogue.segFree (by decide))) ?_
      cases ok
      · exact SegU.of_seg (seg_jmp (pc := Site.pc $s + 2) $jump (braFree _ _ _)
          (Epilogue.segFree (by decide)))
      · dsimp only [code, Softmax.facts, ↓reduceIte]
        seg_ctl rules_frame, hooks_ok))

theorem stepAt_wqU {p L g} (v : V) : (code p L g).StepAtU ⟨.wq,v,0,[]⟩ := by
  poll_at (.wq) to (.ws .first) via Flow.code_3420, Flow.code_3421, Flow.code_3422

theorem stepAt_ws_firstU {p L g} (v : V) : (code p L g).StepAtU ⟨.ws .first,v,0,[]⟩ := by
  poll_at (.ws .first) to (.sld .first 0) via Flow.code_3425, Flow.code_3426, Flow.code_3427

theorem stepAt_ws_biasU {p L g} (v : V) : (code p L g).StepAtU ⟨.ws .bias,v,0,[]⟩ := by
  poll_at (.ws .bias) to (.sld .bias 0) via Flow.code_5109, Flow.code_5110, Flow.code_5111

theorem stepAt_ws_plainU {p L g} (v : V) : (code p L g).StepAtU ⟨.ws .plain,v,0,[]⟩ := by
  poll_at (.ws .plain) to (.sld .plain 0) via Flow.code_6676, Flow.code_6677, Flow.code_6678

theorem stepAt_wb_firstU {p L g} (v : V) : (code p L g).StepAtU ⟨.wb false,v,0,[]⟩ := by
  poll_at (.wb false) to (.bld false 0) via Flow.code_3498, Flow.code_3499, Flow.code_3500

theorem stepAt_wb_biasU {p L g} (v : V) : (code p L g).StepAtU ⟨.wb true,v,0,[]⟩ := by
  poll_at (.wb true) to (.bld true 0) via Flow.code_5181, Flow.code_5182, Flow.code_5183

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
