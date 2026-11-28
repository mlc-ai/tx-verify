-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Lemmas.Flow.OutKinds
import Kernels.InklingRelDecode.Proof.Softmax.Data.HalfWin
import Kernels.InklingRelDecode.Proof.Softmax.GenRules
import Kernels.InklingRelDecode.Proof.Lib.FloatRules
import Kernels.InklingRelDecode.Proof.Lib.WinLane
import Kernels.InklingRelDecode.Flow.Sites.Part000
import Lemmas.Flow.OutRun
import Lemmas.Flow.SetpCore
import Lemmas.Flow.ReadRun
import Lemmas.Flow.Recip
import Lemmas.Flow.FloatRead
import Lemmas.Flow.ShflSrc
import Kernels.InklingRelDecode.Proof.Lib.RcpApprox
import Kernels.InklingRelDecode.Proof.Softmax.Data.RcpReal

/-! # The operand of the reciprocal is not a zero

The epilogue sets `p178` to `l == 0 or NaN` (`setp.equ`, pc 2568) and selects `1.0` or the row sum
`l` by it (`selp`, pc 2601): the reciprocal's operand is `1.0`, or a number the comparison found
different from zero. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption Data Lib

variable {L : Launch} {g : Nat}

set_option maxRecDepth 100000

/-- A local step performed the instruction's execution. -/
private theorem exec_of_tau {b t : TState} {op : Op} (hc : kernel.code[b.pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (h : Tau kernel Assumptions.all L g b t) :
    execLocalA Assumptions.all L g b op = .ok t := by
  unfold Tau out at h
  cases hf : b.fault with
  | some f => simp [hf] at h
  | none =>
    simp only [hf, hc, guardHolds, hl, pure, Except.pure, ↓reduceIte] at h
    cases hx : execLocalA Assumptions.all L g b op with
    | error f => simp [hx] at h
    | ok u =>
      simp only [hx, Out.tau.injEq] at h
      rw [h]

private theorem ofDatum_none {d : Exec FVal} (h : readEReal.ofDatum d = none) :
    ∃ b, d = .ok (.nan b) := by
  rcases d with e | c
  · simp [readEReal.ofDatum] at h
  · rcases c with n | q | n | b <;> simp [readEReal.ofDatum, pure, Except.pure] at h ⊢

private theorem readEReal_none_nan {v : Value} (h : readEReal .f32 v = none) :
    ∃ b, classify .f32 v = .ok (.nan b) := by
  cases v with
  | float f x =>
    by_cases hf : f = .f32
    · simp [readEReal, hf, pure, Except.pure] at h
    · simp only [readEReal, hf, ↓reduceIte] at h
      exact ofDatum_none h
  | _ => exact ofDatum_none (by simpa [readEReal] using h)

/-- **A comparison with zero that is false** reads a number (no NaN, no fault). -/
private theorem setp_false_real {v : Value} {fz : Bool}
    (h : setpE (.unord .eq) fz v (.bits 32 (BitVec.ofNat 64 0)) = .ok false) :
    ∃ x : EReal, readEReal .f32 v = some (.ok x) := by
  rcases hv : readEReal .f32 v with _ | e | x
  · exfalso
    obtain ⟨b, hb⟩ := readEReal_none_nan hv
    unfold setpE idealSetp at h
    simp only [fcmpBase, hv, bindRead] at h
    unfold coreSetp at h
    simp [hb, bind, Except.bind] at h
    have hz : classify .f32 (.bits 32 (BitVec.ofNat 64 0)) = .ok (.zero false) := by rfl
    rw [hz] at h
    cases fz <;> cases b <;> simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.compare,
      FloatInstr.flushIn, FCmp.eval, FVal.isNaN, FloatInstr.srcFmt, Layout.flush, pure,
      Except.pure] at h
  · exfalso
    unfold setpE idealSetp at h
    simp [fcmpBase, hv, bindRead] at h
  · exact ⟨x, rfl⟩

/-- **A comparison with zero that is false** reads a number other than zero. -/
private theorem setp_false_ne {v : Value} {x : EReal}
    (h : setpE (.unord .eq) false v (.bits 32 (BitVec.ofNat 64 0)) = .ok false)
    (hx : readEReal .f32 v = some (.ok x)) : x ≠ 0 := by
  have hz : readEReal .f32 (.bits 32 (BitVec.ofNat 64 0)) = some (.ok 0) := by rfl
  unfold setpE idealSetp at h
  simp only [fcmpBase, hx, hz, bindRead] at h
  intro h0
  subst h0
  simp [erealCompare, pure, Except.pure] at h

/-- **The selection of pc 2601** picks `1.0` or the row sum by the predicate. -/
private theorem selp_tau {b t : TState} (hpc : b.pc = 2601)
    (hc : kernel.code[b.pc]? =
      some ⟨none, (OItem.selp 1762 (.f32imm 1065353216) (.reg 1915) 178).op⟩)
    (h : Tau kernel Assumptions.all L g b t) :
    ∃ pick, b.regs 178 = some (.pred pick) ∧
      (pick = true → t.regs 1762 = some (.bits 32 (BitVec.ofNat 64 1065353216))) ∧
      (pick = false → ∃ v, b.regs 1915 = some v ∧ t.regs 1762 = some v) := by
  have hx := exec_of_tau hc rfl h
  have hR : NoLocalRule Assumptions.all L g 2601
      (OItem.selp 1762 (.f32imm 1065353216) (.reg 1915) 178).op :=
    noRuleAt 2601 ⟨by omega, by omega, by omega⟩ (by rfl)
  have hS : Assumption.SegFreePc Assumptions.all b.pc := hpc ▸ segFree (by decide)
  have hRb := hR b hpc
  simp only [OItem.op] at hRb
  simp only [OItem.op, hS.exec rfl, execLocalRule_of_none hRb,
    execLocal_selp (i := ⟨.selp, .float .f32, false, [some 1762], [.f32imm 1065353216, .reg 1915,
      .reg 178]⟩) rfl, execMove, DType.width, readReg] at hx
  cases hp : b.regs 178 with
  | none => simp [hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hx
  | some pv =>
    cases pv with
    | pred pick =>
      refine ⟨pick, rfl, fun hq => ?_, fun hq => ?_⟩
      · subst hq
        simp [hp, readValue, readBits, bind, Except.bind, pure, Except.pure, Value.bytes] at hx
        subst hx
        simp [next, setReg]
      · subst hq
        cases hq' : b.regs 1915 with
        | none => simp [hp, hq', readValue, readReg, bind, Except.bind, pure, Except.pure,
            throw, throwThe, MonadExceptOf.throw] at hx
        | some v =>
          simp [hp, hq', readValue, readReg, bind, Except.bind, pure, Except.pure,
            throw, throwThe, MonadExceptOf.throw] at hx
          by_cases h4 : v.bytes = 4
          · simp only [h4, ↓reduceIte] at hx
            have e : next (setReg b 1762 v) = t := Except.ok.inj hx
            subst e
            exact ⟨v, rfl, by simp [next, setReg]⟩
          · simp only [h4, ↓reduceIte] at hx
            cases hx
    | _ => simp [hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
        Except.pure] at hx

/-- **The comparison of pc 2568** writes its outcome, when the row sum is defined. -/
private theorem setp_tau {c w : TState} (hpc : c.pc = 2568)
    (hc : kernel.code[c.pc]? = some ⟨none, (OItem.setp (.unord .eq) false 178 1915 0).op⟩)
    (hd : ∃ v, c.regs 1915 = some v) (h : Tau kernel Assumptions.all L g c w) :
    ∃ v, c.regs 1915 = some v ∧ ∃ r, setpE (.unord .eq) false v (.bits 32 (BitVec.ofNat 64 0)) =
      .ok r ∧ w.regs 178 = some (.pred r) := by
  obtain ⟨v, hv⟩ := hd
  have hx := exec_of_tau hc rfl h
  have hem : Assumptions.emuSites.contains c.pc = false := by rw [hpc]; decide
  have hf0 : setpForm 0 = .setp .f32 := rfl
  have hR : (OItem.setp (.unord .eq) false 178 1915 0).Rule Assumptions.all L g c := by
    refine ⟨?_, ?_⟩
    · rw [hf0]
      exact ideal_at (by simp [idealForms]) hem
    · rw [hf0]
      exact decline_at (by simp [idealForms]) hem (by omega) (by omega) (by omega)
  have hex := OItem.exec (OItem.setp (.unord .eq) false 178 1915 0)
    (V := fun r => (c.regs r).getD dflt) (segFree hem) hR
    (fun r hr => by
      simp only [OItem.reads, List.mem_singleton] at hr
      subst hr
      simp [hv]) rfl
  by_cases hcnd : (OItem.setp (.unord .eq) false 178 1915 0).cond (fun r => (c.regs r).getD dflt)
  · have e := hex.1 hcnd
    rw [hx] at e
    obtain rfl := Except.ok.inj e
    obtain ⟨r, hr⟩ := hcnd
    have hr' : setpE (.unord .eq) false v (.bits 32 (BitVec.ofNat 64 0)) = .ok r := by
      simpa [hv] using hr
    refine ⟨v, hv, r, hr', ?_⟩
    simp [OItem.post, OItem.vals, setReg, PTX.next, okPred, hv, hr']
  · obtain ⟨f, hf⟩ := hex.2 hcnd
    rw [hx] at hf
    cases hf

private def rLo : List (Nat × Nat) := [(576, 948), (1013, 1261), (2560, 2565)]
private def rHi : List (Nat × Nat) := [(2603, 2603), (2609, 2846)]
private def rP : List (Nat × Nat) := [(2569, 2602)]
private def rS : List (Nat × Nat) := [(2569, 2603), (2674, 2846)]

private theorem rlo_fwd : fwdOk rLo [] = true := by decide +kernel
private theorem rhi_fwd : fwdOk rHi [] = true := by decide +kernel
private theorem rp_enter : enterOk rP 2569 = true := by decide +kernel
private theorem rs_fwd : fwdOk rS [178, 1915] = true := by decide +kernel
private theorem ce_late : ∀ q ∈ entryEvents ceWin, q ≤ 2565 ∨ 2603 ≤ q := by decide +kernel
private theorem code_2568 : kernel.code[2568]? =
    some ⟨none, (OItem.setp (.unord .eq) false 178 1915 0).op⟩ :=
  OItem.instrB_eq (by decide +kernel)
private theorem code_2601 : kernel.code[2601]? =
    some ⟨none, (OItem.selp 1762 (.f32imm 1065353216) (.reg 1915) 178).op⟩ :=
  OItem.instrB_eq (by decide +kernel)
private theorem no_write : 1915 ∉ writesRegs (OItem.setp (.unord .eq) false 178 1915 0).op := by
  decide +kernel

private theorem pred_scan : scanCode (fun pc ins =>
    ((Lib.succs pc ins.op) ++ (if ins.guard.isSome then [pc + 1] else [])).all fun q =>
      !(q == 2569 || q == 2602 || q == 2603) || (pc + 1 == q)) kernel.code 0 = true := by
  decide +kernel

private theorem pred_pc {b t : TState} (h : Tau kernel Assumptions.all L g b t)
    (hq : t.pc = 2569 ∨ t.pc = 2602 ∨ t.pc = 2603) : b.pc + 1 = t.pc := by
  obtain ⟨ins, hc, -, hk⟩ := win_cases h
  have hsc := scanCode_get pred_scan hc
  rw [Nat.zero_add] at hsc
  rcases hk with ⟨-, hp, -⟩ | ⟨-, hp, -⟩
  · omega
  · have := List.all_eq_true.mp hsc t.pc (by simp [hp])
    simp at this
    omega

/-- **The operand of the reciprocal at pc 2602 reads as a number other than zero.** -/
public theorem rcp_late_ex {X : Execution} {t : TState} (hl : Iface.LaneState L X g t)
    (hpc : t.pc = 2602) :
    ∃ y : EReal, readERealOpnd t .f32 (.reg 1762) = some (.ok y) ∧ y ≠ 0 := by
  have hin : inS ceWin t.pc = true := by simp [inS, ceWin, hpc]
  obtain ⟨k, e, t0, hk, hr1, ⟨s, hes⟩, hev, hin0, hrt, -⟩ := lane_set ce_fwd ce_enter ce_zero hl hin
  have hpost := post_pc hes
  have hspc := EventFrame.estep_source_pc hes
  simp only [inS, ceWin, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    decide_eq_true_eq] at hin0
  have h65 : e.pc = 2565 := by
    rcases ce_late e.pc hev with h | h
    · by_contra hne
      have h1 : inS rLo t0.pc = true := by simp only [inS, rLo]; simp; omega
      have := (win_keep rlo_fwd hrt h1).1
      simp only [inS, rLo] at this; simp at this; omega
    · exfalso
      have h1 : inS rHi t0.pc = true := by simp only [inS, rHi]; simp; omega
      have := (win_keep rhi_fwd hrt h1).1
      simp only [inS, rHi] at this; simp at this; omega
  have ht0 : t0.pc = 2566 := by
    rcases (by omega : t0.pc = 2565 ∨ t0.pc = 2566) with h | h
    · exfalso
      rcases Relation.ReflTransGen.cases_head hrt with h0 | ⟨c, hc, -⟩
      · subst h0; omega
      · exact no_tau_evAt (by rw [h]; decide +kernel) hc
    · exact h
  have hu : inS rP t0.pc = false := by simp [inS, rP]; omega
  have hv : inS rP t.pc = true := by simp [inS, rP, hpc]
  obtain ⟨w, hw1, hw2, hwpc, hwin⟩ := first_entry rp_enter hrt hu hv
  rcases Relation.ReflTransGen.cases_tail hw1 with h0 | ⟨c, hc1, hcw⟩
  · subst h0; omega
  rcases Relation.ReflTransGen.cases_tail hw2 with h0 | ⟨b, hb1, hbt⟩
  · subst h0; omega
  have hcpc : c.pc = 2568 := by have := pred_pc hcw (Or.inl hwpc); omega
  have hbpc : b.pc = 2601 := by have := pred_pc hbt (Or.inr (Or.inl hpc)); omega
  have hw' : inS rS w.pc = true := by simp [inS, rS, hwpc]
  obtain ⟨-, hkeep⟩ := win_keep rs_fwd hb1 hw'
  have hb178 : b.regs 178 = w.regs 178 := hkeep 178 (by simp)
  have hb1915 : b.regs 1915 = w.regs 1915 := hkeep 1915 (by simp)
  have hc2568 : kernel.code[c.pc]? =
      some ⟨none, (OItem.setp (.unord .eq) false 178 1915 0).op⟩ := by
    rw [hcpc]; exact code_2568
  have hb2601 : kernel.code[b.pc]? = some ⟨none, (OItem.selp 1762 (.f32imm 1065353216)
      (.reg 1915) 178).op⟩ := by
    rw [hbpc]; exact code_2601
  obtain ⟨pick, hpick, hT, hF⟩ := selp_tau hbpc hb2601 hbt
  rw [hb178] at hpick
  have hcw1915 : w.regs 1915 = c.regs 1915 := by
    obtain ⟨ins, hci, -, hk⟩ := win_cases hcw
    obtain rfl : ins = ⟨none, (OItem.setp (.unord .eq) false 178 1915 0).op⟩ :=
      Option.some.inj (hci.symm.trans hc2568)
    rcases hk with ⟨hg, -⟩ | ⟨-, -, hk'⟩
    · simp at hg
    · exact hk' 1915 no_write (fun h => by rw [show c.pc = 2568 from hcpc] at h; cases h)
  cases pick with
  | true =>
    have h1 := hT rfl
    have h2 : readEReal .f32 (.bits 32 (BitVec.ofNat 64 1065353216)) = some (.ok 1) :=
      readEReal_of_valFloat valFloat_one
    refine ⟨1, ?_, one_ne_zero⟩
    simp only [readERealOpnd, readReg, h1, pure, Except.pure, h2]
  | false =>
    obtain ⟨v, hv, ht⟩ := hF rfl
    have hcv : c.regs 1915 = some v := by rw [← hcw1915, ← hb1915]; exact hv
    obtain ⟨v', hv', r, hr, hw178⟩ := setp_tau hcpc hc2568 ⟨v, hcv⟩ hcw
    rw [hcv] at hv'
    obtain rfl := Option.some.inj hv'
    rw [hpick] at hw178
    obtain rfl : false = r := Value.pred.inj (Option.some.inj hw178)
    obtain ⟨x, hx⟩ := setp_false_real hr
    refine ⟨x, ?_, setp_false_ne hr hx⟩
    simp only [readERealOpnd, readReg, ht, pure, Except.pure, hx]

/-- **The operand of the reciprocal at pc 2602 is not a zero** (`Iface.LateValues.rcp`). -/
public theorem rcp_late {X : Execution} {t : TState} (hl : Iface.LaneState L X g t)
    (hpc : t.pc = 2602) :
    ∀ x : EReal, readERealOpnd t .f32 (.reg 1762) = some (.ok x) → x ≠ 0 := fun x hx => by
  obtain ⟨y, hy, h0⟩ := rcp_late_ex hl hpc
  obtain rfl := Except.ok.inj (Option.some.inj (hy.symm.trans hx))
  exact h0

/-- **The state at pc 2603 comes from the state at pc 2602 by a local step.** -/
public theorem rcp_pred {X : Execution} {t : TState} (hl : Iface.LaneState L X g t)
    (hpc : t.pc = 2603) :
    ∃ c, Iface.LaneState L X g c ∧ c.pc = 2602 ∧ Tau kernel Assumptions.all L g c t := by
  have hin : inS ceWin t.pc = true := by simp [inS, ceWin, hpc]
  obtain ⟨k, e, t0, hk, hr1, ⟨s, hes⟩, hev, hin0, hrt, -⟩ := lane_set ce_fwd ce_enter ce_zero hl hin
  rcases Relation.ReflTransGen.cases_tail hrt with h0 | ⟨c, hc1, hct⟩
  · exfalso
    subst h0
    have hpost := post_pc hes
    have hspc := EventFrame.estep_source_pc hes
    have h3 : s.pc = 2603 := by
      rcases ce_late e.pc (by simpa [entryEvents] using hev) with h | h <;> omega
    obtain ⟨ins, hci, -, hf⟩ := EventFrame.estep_event_source hes
    rw [h3, Flow.code_shfl_15] at hci
    obtain rfl := (Option.some.inj hci).symm
    obtain ⟨_, _, _, _, _, -, -, ht⟩ := fires_shfl_src (p := none) hf
    have := congrArg TState.pc ht
    simp [PTX.next, setReg, h3, hpc] at this
  · exact ⟨c, ⟨k + 1, t0, hr1, hc1⟩, by have := pred_pc hct (Or.inr (Or.inr hpc)); omega, hct⟩

/-- **The reciprocal at pc 2602 is a number**: at pc 2603 the register 1761 holds one. -/
public theorem rcp_word {X : Execution} {t : TState} (hl : Iface.LaneState L X g t)
    (hpc : t.pc = 2603) : ∃ v, t.regs 1761 = some v ∧ SK.fl.Has v := by
  obtain ⟨c, hlc, hcpc, hT⟩ := rcp_pred hl hpc
  obtain ⟨y, hy, hy0⟩ := rcp_late_ex hlc hcpc
  obtain ⟨va, hva⟩ : ∃ va, c.regs 1762 = some va := by
    cases hr : c.regs 1762 with
    | none => simp [readERealOpnd, readReg, hr, throw, throwThe, MonadExceptOf.throw] at hy
    | some va => exact ⟨va, rfl⟩
  have hy' : readEReal .f32 va = some (.ok y) := by
    simpa [readERealOpnd, readReg, hva, pure, Except.pure] using hy
  have hc : kernel.code[c.pc]? = some ⟨none,
      .float { rcpI true with dsts := [some 1761], srcs := [.reg 1762] }⟩ := by
    rw [hcpc]; exact Flow.code_2602
  have hx := exec_of_tau hc rfl hT
  obtain ⟨hA, hD⟩ := Lib.approx_2602 (L := L) (g := g) hcpc
  rw [exec_rcpE hA hD (OpndIs.reg hva)] at hx
  obtain ⟨v, hv, hdv⟩ := Data.rcpE_real true hy' hy0
  rw [hv] at hx
  obtain rfl : PTX.next (setReg c 1761 v) = t := Except.ok.inj hx
  exact ⟨v, by simp [PTX.next, setReg], hdv⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
