-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Proof.Softmax.Data.LaneStopO
import Kernels.InklingRelDecode.Proof.Softmax.Data.Decline
import Kernels.InklingRelDecode.Proof.Softmax.Data.Rescale
import Kernels.InklingRelDecode.Proof.Softmax.Data.RoundNum
import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaNum

/-! # The rescale multiplications are not declined

The 64 `mul.f32` of pcs 2262 to 2325 multiply the rescale factor (register 507) by the words the
accumulator load of pc 2260 returned (registers 1547 and on). Both are numbers: the factor is
`alphaVal` of a number or `-inf`, the words come from the load (`OTyp`). The state before the wait
of pc 2261 has them, the window keeps them, and the product of two numbers is defined. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption Data Lib

variable {Q : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000

private def rsWin : List (Nat × Nat) := [(2262, 2326)]
private def rsR : List Nat := 507 :: ovRegs

private theorem rs_fwd : fwdOk rsWin rsR = true := by decide +kernel
private theorem rs_enter : enterOk rsWin 0 = true := by decide +kernel
private theorem rs_zero : inS rsWin 0 = false := by decide +kernel
private theorem rs_events : ∀ q ∈ entryEvents rsWin, q = 2261 ∨ q = 2326 := by decide +kernel
private theorem rs_keep : (match kernel.code[2261]? with
    | some ins => rsR.all (fun r => !(EventFrame.eventWrites ins.op).contains r)
    | none => true) = true := by decide +kernel
private theorem rs_ev : evAtB kernel 2326 = true := by decide +kernel

private theorem rs_site (s : Site) (h : s.pc = 2261) : s = .waitLdO := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem rs_scan : scanCode (fun pc ins =>
    !(decide (2262 ≤ pc) && decide (pc ≤ 2325)) || match ins.op with
      | .float f => arith2 .mul 1 f (.reg 507) (.reg (1547 + (pc - 2262)))
      | _ => false) kernel.code 0 = true := by
  decide +kernel

private theorem rs0_mem (V : Nat → Value) {r : Nat} (h1 : 1547 ≤ r) (h2 : r < 1611) :
    (r, V r) ∈ Gen.rs_facts0 V := by
  interval_cases r <;> simp [Gen.rs_facts0]

private theorem rs0_507 (V : Nat → Value) : (507, V 507) ∈ Gen.rs_facts0 V := by
  simp [Gen.rs_facts0]

private theorem mem_dF {ent : Control.Entry} {y : Data.D} {p : Nat × Value} (h : p ∈ dF L y) :
    p ∈ (codeS ent L g).facts y := by
  exact List.mem_append_left _ (List.mem_append_right _ h)

/-- **The rescale multiplication of the pcs 2262 to 2325 is not declined.** -/
public theorem rescale_decl {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (hO : ∀ k a vals sh, X.get (g, k) = some ⟨2260, .tc (.ld a vals sh)⟩ → ∀ x ∈ vals,
      SK.fl.Has x)
    (lane : g % L.block < 128) (hl : Iface.LaneState L X g t) (h1 : 2262 ≤ t.pc)
    (h2 : t.pc ≤ 2325) {i : Instr} (hc : kernel.code[t.pc]? = some i) :
    execIdealFloat L g t i.op ≠ none := by
  have hin : inS rsWin t.pc = true := by simp only [inS, rsWin]; simp; omega
  obtain ⟨k, e, t0, hk, hr1, ⟨s, hes⟩, hev, hin0, hrt, hkeep⟩ :=
    lane_set rs_fwd rs_enter rs_zero hl hin
  have hpost := post_pc hes
  have h61 : e.pc = 2261 := by
    rcases rs_events e.pc (by simpa [entryEvents] using hev) with h | h
    · exact h
    · exfalso
      have h0 : t0.pc = 2326 := by
        have := EventFrame.estep_source_pc hes
        simp only [inS, rsWin] at hin0; simp at hin0; omega
      rcases Relation.ReflTransGen.cases_head hrt with rfl | ⟨c1, hc1, -⟩
      · omega
      · exact no_tau_evAt (by rw [h0]; exact rs_ev) hc1
  have get : X.get (g, k) = some e := hk
  obtain ⟨ent, y, sp, hsite, hat, hes', ni, ot⟩ := lane_stop_o hp hX hf hS h5 hO lane get hr1
    (by omega) (by omega)
  have hy := rs_site _ (hsite.trans h61)
  obtain ⟨-, -, -, -, hreg⟩ := hat
  have hsp : ∀ r, (r, rsV L y.v r) ∈ Gen.rs_facts0 (rsV L y.v) → sp.regs r = some (rsV L y.v r) :=
    fun r hm => holds_mem hreg (mem_dF (by simp only [dF, dFS, hy]; exact hm))
  have ht0 : ∀ r ∈ rsR, t0.regs r = sp.regs r := fun r hr => by
    obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes'
    have spc := EventFrame.estep_source_pc hes'
    have hkp : (match kernel.code[e.pc]? with
        | some ins => rsR.all (fun r => !(EventFrame.eventWrites ins.op).contains r)
        | none => true) = true := by rw [h61]; exact rs_keep
    rw [spc, hci] at hkp
    exact estep_keeps hes' ins hci r (by simpa using List.all_eq_true.mp hkp r hr)
  have hv : ∀ r ∈ rsR, ∃ x : ℝ, readERealOpnd t .f32 (.reg r) = some (.ok (x : EReal)) := by
    intro r hr
    have hr' := hr
    simp only [rsR, List.mem_cons, ovRegs, List.mem_map, List.mem_range] at hr'
    have hm : (r, rsV L y.v r) ∈ Gen.rs_facts0 (rsV L y.v) := by
      rcases hr' with rfl | ⟨j, hj, rfl⟩
      · exact rs0_507 _
      · exact rs0_mem _ (by omega) (by omega)
    have ht : t.regs r = some (rsV L y.v r) := by rw [hkeep r hr, ht0 r hr]; exact hsp r hm
    have hfl : SK.fl.Has (rsV L y.v r) := by
      rcases hr' with rfl | ⟨j, hj, rfl⟩
      · rw [show rsV L y.v 507 = Lib.alphaVal (scaleW L) y.v.m y.v.mx 507 by simp [rsV]]
        exact alpha_real (scaleW_has hp) ni.m ni.mx
      · have e : rsV L y.v (1547 + j) = y.v.ov.getD j (b32 0) := by
          simp [rsV, show 1547 ≤ 1547 + j ∧ 1547 + j < 1611 by omega]
        rw [e]
        by_cases hj' : j < y.v.ov.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
          exact ot _ (List.getElem_mem hj')
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
          exact zero_has
    obtain ⟨x, hx⟩ := SK.reads_fl (k := .fl) rfl hfl
    exact ⟨x, by rw [readERealOpnd_reg ht, hx]⟩
  have hs := scanCode_get rs_scan hc
  rw [Nat.zero_add] at hs
  rcases Bool.or_eq_true_iff.1 hs with hs | hs
  · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hs
    omega
  cases hop : i.op with
  | float f =>
    rw [hop] at hs
    obtain ⟨x, hx⟩ := hv 507 (by simp [rsR])
    obtain ⟨y', hy'⟩ := hv (1547 + (t.pc - 2262)) (by
      simp only [rsR, List.mem_cons, ovRegs, List.mem_map, List.mem_range]
      exact Or.inr ⟨t.pc - 2262, by omega, rfl⟩)
    exact ideal_mul1 hs hx hy' (mulEReal_real _ _)
  | _ => rw [hop] at hs; simp at hs

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
