-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.SafePtc
import Kernels.InklingRelDecode.Flow.Code.Part008

@[expose] public section

/-! # No site of the prologue is undefined behaviour

`safe_pro`: the event template of every site of the prologue but the exit, at a state that holds
its facts and whose request words, broadcast word, block-table words and query halves are typed
(`Ok`), is not undefined behaviour. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The sites whose instruction has no register operand. -/
def staticSite : Site → Bool
  | .sMax | .el _ | .fnc0 | .bar2 | .pb _ _ | .pel _ _ | .fnc1 | .bar18 => true
  | _ => false

theorem static_ok (s : Site) (h : staticSite s = true) : staticAt s.pc = true := by
  cases s <;> simp only [staticSite] at h <;> try exact absurd h (by decide)
  all_goals repeat' (rename_i j; revert j)
  all_goals decide +kernel

/-- **No site of the prologue but the exit is undefined behaviour.** -/
theorem safe_pro {m} (hp : Pre Q L m) (hg : g < L.threads) (hlane : g % L.block < 128)
    {d : Data.D} {t : TState} {ins : Instr} (hat : (Data.code Q L g w).AtD d t)
    (hk : Ok Q L g d) (hs : d.c.site ≠ .exit) (hc : kernel.code[d.c.site.pc]? = some ins)
    (f : Fault) : eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  by_cases hst : staticSite d.c.site = true
  · exact static_tmpl hb (static_ok _ hst) hc f
  · cases hsite : d.c.site with
    | ld i => exact safe_ld hp hg hat hsite hc f
    | lb b h => exact safe_lb hp hat hsite hc f
    | ldq j => exact safe_ldq hp hat hsite hc f
    | init i => exact safe_init hp hat hsite hc f
    | arr b => exact safe_arr hp hat hsite hc f
    | psh b => exact safe_psh hb hat hsite hc f
    | ptc b j => exact safe_ptc hp hg hat hsite hc f
    | stq i j => exact safe_stq hp hlane hat hk hsite hc f
    | st8 => exact safe_st8 hp hat hsite hc f
    | st9 j => exact safe_st9 hp hat hsite hc f
    | exit => exact absurd hsite hs
    | _ => exact absurd (by rw [hsite]; rfl) hst

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
