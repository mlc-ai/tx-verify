-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.LdWait
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.Softmax.Align
public import Kernels.TmlFa4Fwd.Proof.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
public import Kernels.TmlFa4Fwd.Proof.Softmax.Open
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.TmplOkSync
public import Lemmas.Flow.UbFree
import Kernels.TmlFa4Fwd.Flow.Code.Part048
import Kernels.TmlFa4Fwd.Flow.Code.Part049
import Kernels.TmlFa4Fwd.Flow.Code.Part052
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part080
import Kernels.TmlFa4Fwd.Flow.Code.Part101
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part105
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Kernels.TmlFa4Fwd.Flow.Code.Part119
import Kernels.TmlFa4Fwd.Flow.Code.Part120
import Tactics.KernelRfl

@[expose] public section

/-! # The softmax sites whose event could fault, without undefined behaviour

At every site whose shape admits undefined behaviour, except the stores of data registers, the
template of the fired instruction is not undefined behaviour under the facts (`NoUb` as a shape
table, so `Code.ShapeAt` states it): the warp barrier and the election (full masks), the CTA
barrier's arrival (immediate operands), the store waits, the implicit waits of the plain rounds'
score loads and of the delayed P stores (whole warps), the score loads (an address word in the
warp's lane chunk) and the scheduler's and the request's global loads (4-aligned addresses). The
bias loads are in `SafeBld.lean`. An undefined-behaviour event fires only from such a template
(`fires_ub`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A register's value at a state, through every table of the role. -/
macro "soft_val'" : tactic => `(tactic| (
  simp only [valueOf, values, valuesStart, valuesRole, valuesScan, valuesSelect, valuesSelect2,
    valuesReq, valuesTile, valuesP1, valuesBias, valuesPlain, valuesFin, Epilogue.partials,
    Epilogue.loopRegs, Epilogue.lanePreds, sbSi, lookupLit, Option.getD_some, Option.getD_none]
    <;> rfl))

/-- The score loads' Tensor Memory address facts. -/
macro "tm_addr" : tactic => `(tactic| first
  | with_reducible exact (tm_ok ‹Pre _ _ _›).1
  | with_reducible exact (tm_ok ‹Pre _ _ _›).2.1
  | with_reducible exact (tm_ok ‹Pre _ _ _›).2.2.1
  | with_reducible exact (tm_ok ‹Pre _ _ _›).2.2.2)

set_option hygiene false in
/-- The start of a safety obligation: the fired event's template is undefined behaviour. -/
macro "safe_intro" : tactic => `(tactic| (
  intro t ins e o hat hi hc hf f hk
  have h := PTX.Flow.fires_ub hf hk
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have hF := hat.2.2.2.2))

set_option hygiene false in
/-- Instructions whose template has no fault in a launch of whole warps. -/
macro "safe_plain" : tactic => `(tactic| (
  safe_intro
  first
  | exact PTX.Flow.warpBar_ok f h
  | exact PTX.Flow.elect_imm_ok f h
  | exact PTX.Flow.barArrive_imm_ok (by decide) (by decide) (by decide) (by decide) f h
  | exact PTX.Flow.plainOk_tmpl (by rw [‹Pre _ _ _›.block]) rfl f h
  | exact PTX.Flow.tcLd_wait_ok
      (by rw [hat.1]; ld_wait)
      (by rw [hat.2.1]; exact Nat.succ_ne_zero 0) f h
  | exact PTX.Flow.tcSt_wait_ok (by rw [‹Pre _ _ _›.block])
      (by rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl)
      (hat.2.1.trans rfl) f h))

set_option hygiene false in
/-- A score load: its address register is the stage's column base in the warp's lane chunk. -/
macro "safe_tcld" : tactic => `(tactic| (
  safe_intro
  refine' PTX.Flow.tcLd_word_ok ?hb ?hn ?hr ?ha ?hs f h
  case hr => exact (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans (by soft_val')
  case hb => rw [‹Pre _ _ _›.block]
  case hn => decide
  case ha => first | with_reducible exact or32_lt _ _ | with_reducible exact ori_lt _ _
  case hs => tm_addr))

set_option hygiene false in
/-- A global load of the scheduler's or the request's word through register `r`, which holds the
address `v` (an `addrU` or `addrS` of a 4-aligned base, `al` its 4-alignment). -/
macro "safe_ldg" r:term:max v:term:max al:term:max : tactic => `(tactic| (
  safe_intro
  rw [eventTmpl, PTX.memTmpl_load rfl rfl rfl rfl rfl] at h
  have hr : t.regs $r = some $v :=
    (PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans (by soft_val')
  exact ldG_ok hr ($al rfl) (by decide) f h))

set_option hygiene false in
/-- A bias load: a shared vector load at a 16-aligned swizzled address. -/
macro "safe_lds" : tactic => `(tactic| (
  safe_intro
  rw [eventTmpl, PTX.memTmpl_load rfl rfl rfl rfl rfl] at h
  refine PTX.Flow.ldShared4_ok ((PTX.Flow.regs_of_factsFrom hF (by lit_mem)).trans (by soft_val'))
    ?_ f h
  rw [Nat.add_mod]
  simp (disch := decide) only [lo_bAddr ‹Pre _ _ _›, lo_bAddr0 ‹Pre _ _ _›]
  decide))

set_option maxHeartbeats 4000000
variable (hp : Pre p L m)
include hp
set_option linter.unusedSectionVars false

theorem safe_pws (r : Rd) (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.pws r, v, 0, acc⟩ := by
  cases r <;> safe_plain

theorem safe_pel (r : Rd) (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.pel r, v, 0, acc⟩ := by
  cases r <;> safe_plain

theorem safe_barEnd (l : Bool) (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.barEnd l, v, 0, acc⟩ := by
  cases l <;> safe_plain

theorem safe_pwst (r : Rd) (j : Fin 2) (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.pwst r j, v, 0, acc⟩ := by
  cases r <;> fin_cases j <;> safe_plain

theorem safe_sldw (c : Fin 4) (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.sldw c, v, 1, acc⟩ := by
  fin_cases c <;> safe_plain

theorem safe_pstw (b : Bool) (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.pst (rdOf b) 0, v, 0, acc⟩ := by
  cases b <;> safe_plain

theorem safe_sld (r : Rd) (c : Fin 4) (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.sld r c, v, 0, acc⟩ := by
  cases r <;> fin_cases c <;> safe_tcld

theorem safe_word (k : Epilogue.Scan) (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.word k, v, 0, acc⟩ := by
  have hq := ‹Pre _ _ _›.alignment.2.2.2.2.2.2.2.2.1
  cases k
  · safe_ldg 7888 (Epilogue.addrU p.cuQBase (Epilogue.laneW L g)) (addrU_al hq)
  · safe_ldg 7890 (Epilogue.addrS p.cuQBase (Epilogue.reqOf L g v.sc.grp)) (addrS_al hq)
  · safe_ldg 8982 (Epilogue.addrU p.cuQBase (Epilogue.laneW L g)) (addrU_al hq)
  · safe_ldg 8984 (Epilogue.addrS p.cuQBase (Epilogue.reqOf L g v.sc.grp)) (addrS_al hq)

theorem safe_req (v : V) (acc : List Value) :
    (code p L g).ShapeAt NoUb ⟨.q0, v, 0, acc⟩ ∧ (code p L g).ShapeAt NoUb ⟨.q1, v, 0, acc⟩ ∧
    (code p L g).ShapeAt NoUb ⟨.uk, v, 0, acc⟩ := by
  have hq := ‹Pre _ _ _›.alignment.2.2.2.2.2.2.2.2.1
  have hu := ‹Pre _ _ _›.alignment.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · safe_ldg 7892 (Epilogue.addrS p.cuQBase (Epilogue.chosen v.sc)) (addrS_al hq)
  · safe_ldg 7892 (Epilogue.addrS p.cuQBase (Epilogue.chosen v.sc)) (addrS_al hq)
  · safe_ldg 7893 (Epilogue.addrS p.usedKBase (Epilogue.chosen v.sc)) (addrS_al hu)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
