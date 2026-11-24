-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ballot
import Kernels.TmlFa4Fwd.Proof.Correction.Havoc
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Lemmas.Flow.WaitU
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl
import Lemmas.Flow.SegJump

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof

set_option maxRecDepth 100000

private theorem keys {v : Nat → Value} {rs : List Nat} :
    (factsFrom rs v).map Prod.fst = rs := by
  simp only [factsFrom, List.map_map, Function.comp_def]
  exact List.map_id _

set_option hygiene false in
local macro "poll_at " s:term:max " to " doneSite:term:max " via " mem:term:max ","
    branch:term:max "," jump:term:max : tactic =>
  `(tactic| (
    refine Code.waitU (C := code p L g) (dst := fun ok => ⟨if ok then $doneSite else $s,v,0⟩)
      $mem ?_ (fun m q ok s => by cases ok <;> rfl) rfl rfl (fun _ => rfl) (fun _ => rfl)
      (fun _ => .inl rfl) ?_
    · change _ ∉ (factsFrom _ _).map Prod.fst
      rw [keys]
      dsimp only [live, D.site]
      decide +kernel
    · intro ok
      refine SegU.comp (SegU.branch (pc := Site.pc $s + 1) ok $branch bra_rule
        (Epilogue.segFree (by decide))) ?_
      cases ok
      · exact SegU.of_seg (seg_jmp (pc := Site.pc $s + 2) $jump (fun t _ => bra_rule t)
          (Epilogue.segFree (by decide)))
      · dsimp only [code, facts, ↓reduceIte]
        seg_ctl rules_frame, hooks_ok))

theorem stepAt_fwU {p L g} (st k : Fin 2) (v : V) :
    (code p L g).StepAtU ⟨.fw st k,v,0⟩ := by
  fin_cases st <;> fin_cases k
  · poll_at (.fw 0 0) to (.fw 0 1) via Flow.code_8473, Flow.code_8474, Flow.code_8475
  · poll_at (.fw 0 1) to (.fld 0 0) via Flow.code_8476, Flow.code_8477, Flow.code_8478
  · poll_at (.fw 1 0) to (.fw 1 1) via Flow.code_8769, Flow.code_8770, Flow.code_8771
  · poll_at (.fw 1 1) to (.fld 1 0) via Flow.code_8772, Flow.code_8773, Flow.code_8774

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
