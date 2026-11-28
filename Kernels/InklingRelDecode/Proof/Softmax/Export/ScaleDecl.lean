-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Proof.Lib.WinKeep
import Kernels.InklingRelDecode.Proof.Softmax.Data.LaneStop
import Kernels.InklingRelDecode.Proof.Softmax.Data.Decline
import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants

/-! # The scale multiplication of pc 601 is not declined

`mul.f32` of the scale register (525, the launch's scale parameter) by a constant. The register is
a datum of the launch (`scaleVal_float`), kept from the state before the setup's first barrier to
pc 601, and the constant is a number. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption Data Lib

variable {Q : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000

private def scWin : List (Nat × Nat) := [(576, 601)]

private theorem sc_keep : keepOk scWin [525] = true := by decide +kernel
private theorem sc_enter : enterOk scWin 0 = true := by decide +kernel
private theorem sc_zero : inS scWin 0 = false := by decide +kernel
private theorem sc_events : ∀ q ∈ entryEvents scWin, q = 575 := by decide +kernel
private theorem sc_ev : (match kernel.code[575]? with
    | some ins => [525].all (fun r => !(EventFrame.eventWrites ins.op).contains r)
    | none => true) = true := by decide +kernel
private theorem sc_code : (match kernel.code[601]? with
    | some ins => match ins.op with
      | .float f => arith2 .mul 1 f (.reg 525) (.f32imm 1069066811)
      | _ => false
    | none => false) = true := by decide +kernel

private theorem sc_site (s : Site) (h : s.pc = 575) : s = .setMaxReg ∨ s = .bar0 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The scale multiplication of pc 601 is not declined.** -/
public theorem scale_decl {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hl : Iface.LaneState L X g t) (hpc : t.pc = 601) {i : Instr}
    (hc : kernel.code[t.pc]? = some i) : execIdealFloat L g t i.op ≠ none := by
  have hin : inS scWin t.pc = true := by simp [inS, scWin, hpc]
  obtain ⟨k, e, t0, hk, hr1, ⟨s, hes⟩, hev, hin0, hrt, hkeep⟩ :=
    lane_set_keep sc_keep sc_enter sc_zero hl hin
  have h75 := sc_events e.pc (by simpa [entryEvents] using hev)
  obtain ⟨ent, y, sp, hsite, hat, hes', -⟩ := lane_stop_core hp hX (e := e) hk hr1
    (by omega) (by omega)
  have hy := sc_site _ (hsite.trans h75)
  obtain ⟨-, -, -, -, hreg⟩ := hat
  have hsp : sp.regs 525 = some (scaleVal L) :=
    holds_mem hreg (List.mem_append_left _ (List.mem_append_right _
      (by rcases hy with hy | hy <;> simp [dF, dFS, hy, entryFact])))
  have ht : t.regs 525 = some (scaleVal L) := by
    obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes'
    have spc := EventFrame.estep_source_pc hes'
    have hkp : (match kernel.code[e.pc]? with
        | some ins => [525].all (fun r => !(EventFrame.eventWrites ins.op).contains r)
        | none => true) = true := by rw [h75]; exact sc_ev
    rw [spc, hci] at hkp
    rw [hkeep 525 (by simp), estep_keeps hes' ins hci 525
      (by simpa using List.all_eq_true.mp hkp 525 (by simp))]
    exact hsp
  rw [hpc] at hc
  have hcc := sc_code
  rw [hc] at hcc
  simp only at hcc
  cases hop : i.op with
  | float f =>
    rw [hop] at hcc
    refine ideal_mul1 (x := (Q.scale : EReal)) (y := (log2eF32 : EReal)) hcc ?_ ?_
      (mulEReal_real _ _)
    · rw [readERealOpnd_reg ht]; exact readEReal_of_valFloat (scaleVal_float hp)
    · exact readEReal_of_valFloat valFloat_log2e
  | _ => rw [hop] at hcc; simp at hcc

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
