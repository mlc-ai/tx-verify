-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreSpan
import Kernels.TmlFa4Fwd.Gen.StepCorrection
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.AdvanceU
import Lemmas.Flow.ArriveU
import Lemmas.Flow.IssueNext
import Lemmas.Flow.Step.TcSteps
import Lemmas.Flow.RoleTemplates
import Lemmas.Flow.SegCtl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof

set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g : Nat}

private theorem keys (d : D) :
    ((code p L g).facts d).map Prod.fst = liveAt d.site := by
  change (factsFrom _ _).map Prod.fst = _
  simp only [factsFrom, List.map_map, Function.comp_def]
  exact List.map_id _

set_option hygiene false in
local macro "advance " dst:term " at " lookup:term " by " event:tactic : tactic =>
  `(tactic| refine Code.advanceU (dn := ⟨$dst,v,0⟩) $lookup rfl
    (by intro t u e hf; $event) (fun _ => rfl) rfl rfl rfl rfl (.inl rfl) ?_)

set_option hygiene false in
local macro "arrive " dst:term " at " lookup:term : tactic =>
  `(tactic| refine Code.arriveU (dn := ⟨$dst,v,0⟩) $lookup
    (by rw [keys]; dsimp only [D.site]; decide +kernel) (fun _ => rfl)
    rfl rfl rfl rfl (.inl rfl) ?_)

set_option hygiene false in
local macro "copy_regs " src:term:max " to " dst:term:max : tactic =>
  `(tactic| exact copy_span (p := p) (L := L) (g := g) (v := v) (k := 0)
    (s := $src) (dst := $dst) (by decide +kernel) (by decide +kernel) (fun _ _ => rfl))

theorem stepAt_rbarU (st : Fin 2) (v : V) : (code p L g).StepAtU ⟨.rbar st,v,0⟩ := by
  fin_cases st
  · advance (.rscale 0) at Flow.code_8006 by exact fires_barSyncN_next hf
    copy_regs (.rbar 0) to (.rscale 0)
  · advance (.rscale 1) at Flow.code_8225 by exact fires_barSyncN_next hf
    copy_regs (.rbar 1) to (.rscale 1)

theorem stepAt_rwaitU (st : Fin 2) (v : V) : (code p L g).StepAtU ⟨.rwait st,v,0⟩ := by
  fin_cases st
  · advance (.rarr 0 0) at Flow.code_8221 by exact fires_tcWaitSt_next hf
    dsimp only [code, facts]
    seg_ctl rules_frame, hooks_ok
  · advance (.rarr 1 0) at Flow.code_8440 by exact fires_tcWaitSt_next hf
    dsimp only [code, facts]
    seg_ctl rules_frame, hooks_ok

theorem stepAt_rarr_firstU (st : Fin 2) (v : V) : (code p L g).StepAtU ⟨.rarr st 0,v,0⟩ := by
  fin_cases st
  · arrive (.rarr 0 1) at Flow.code_8223
    copy_regs (.rarr 0 0) to (.rarr 0 1)
  · arrive (.rarr 1 1) at Flow.code_8442
    copy_regs (.rarr 1 0) to (.rarr 1 1)

theorem stepAt_rarr_switchU (v : V) : (code p L g).StepAtU ⟨.rarr 0 1,v,0⟩ := by
  arrive (.rbar 1) at Flow.code_8224
  copy_regs (.rarr 0 1) to (.rbar 1)

theorem stepAt_farr0U (v : V) : (code p L g).StepAtU ⟨.farr0,v,0⟩ := by
  arrive (.fbar 0) at Flow.code_8464
  copy_regs (.farr0) to (.fbar 0)

theorem stepAt_fbarU (st : Fin 2) (v : V) : (code p L g).StepAtU ⟨.fbar st,v,0⟩ := by
  fin_cases st
  · advance (.fsum 0) at Flow.code_8465 by exact fires_barSyncN_next hf
    copy_regs (.fbar 0) to (.fsum 0)
  · advance (.fsum 1) at Flow.code_8761 by exact fires_barSyncN_next hf
    copy_regs (.fbar 1) to (.fsum 1)

theorem stepAt_farrU (st : Fin 2) (v : V) : (code p L g).StepAtU ⟨.farr st,v,0⟩ := by
  fin_cases st
  · arrive (.fw 0 0) at Flow.code_8468
    dsimp only [code, facts]
    seg_ctl rules_frame, hooks_ok
  · arrive (.fw 1 0) at Flow.code_8764
    dsimp only [code, facts]
    seg_ctl rules_frame, hooks_ok

theorem stepAt_fenceU (st : Fin 2) (v : V) : (code p L g).StepAtU ⟨.fence st,v,0⟩ := by
  fin_cases st
  · advance (.fdone 0 0) at Flow.code_8758 by exact Option.some.inj (fires_fence_proxy hf).2
    copy_regs (.fence 0) to (.fdone 0 0)
  · advance (.fdone 1 0) at Flow.code_9054 by exact Option.some.inj (fires_fence_proxy hf).2
    copy_regs (.fence 1) to (.fdone 1 0)

theorem stepAt_fdone_firstU (st : Fin 2) (v : V) :
    (code p L g).StepAtU ⟨.fdone st 0,v,0⟩ := by
  fin_cases st
  · arrive (.fdone 0 1) at Flow.code_8759
    copy_regs (.fdone 0 0) to (.fdone 0 1)
  · arrive (.fdone 1 1) at Flow.code_9055
    copy_regs (.fdone 1 0) to (.fdone 1 1)

theorem stepAt_fdone_switchU (v : V) : (code p L g).StepAtU ⟨.fdone 0 1,v,0⟩ := by
  arrive (.fbar 1) at Flow.code_8760
  copy_regs (.fdone 0 1) to (.fbar 1)

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
