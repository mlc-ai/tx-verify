-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionPollPrefix
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part131

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Mma

noncomputable section

private def rescaleCode (s : TState) (steps : Nat) : Prop :=
  s.pc = 8444 ∧ s.fault = none ∧ s.regs 7278 = some (b32 (2 ^ 32 - steps))

private def nextRescaleSteps (steps : Nat) : Nat :=
  if steps = 1 then 2 ^ 32 else steps - 1

private theorem rescaleCounterRun {l : Launch} {g steps : Nat} {s : TState}
    (h : rescaleCode s steps) (hLo : 1 ≤ steps) (hHi : steps ≤ 2 ^ 32) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      u.pc = (if steps = 2 then 8447 else 8006) ∧ u.fault = none ∧ u.sub ≤ s.sub ∧
      u.regs 7278 = some (b32 (2 ^ 32 - nextRescaleSteps steps)) := by
  obtain ⟨hp, hf, hReg⟩ := h
  let x := 2 ^ 32 - steps
  let y := 2 ^ 32 - nextRescaleSteps steps
  have hx : x < 2 ^ 32 := by dsimp [x]; omega
  have hy : y < 2 ^ 32 := by dsimp [y, nextRescaleSteps]; split <;> omega
  have hInc : truncBits 32 (BitVec.ofNat 64 (x + 1)) = BitVec.ofNat 64 y := by
    by_cases hWrap : steps = 1
    · have hX : x + 1 = 2 ^ 32 := by dsimp [x]; omega
      have hY : y = 0 := by simp [y, nextRescaleSteps, hWrap]
      rw [hX, hY]
      rfl
    · have hEq : x + 1 = y := by dsimp [x, y, nextRescaleSteps]; rw [ite_eq_right hWrap]; omega
      rw [hEq, truncBits_ofNat hy (by decide)]
  have hLast : y = 2 ^ 32 - 1 ↔ steps = 2 := by
    dsimp [y, nextRescaleSteps]
    split <;> omega
  let v := next (setReg s 7278 (b32 y))
  let w := next (setReg v 735 (.pred (decide (steps ≠ 2))))
  have hv : v.pc = 8445 := by simp [v, next, setReg, hp]
  have hw : w.pc = 8446 := by simp [w, next, setReg, hv]
  have hvF : v.fault = none := hf
  have hwF : w.fault = none := hf
  have hReg' : readReg s 7278 = .ok (b32 x) := by
    simp [readReg, hReg, x, pure, Except.pure]
  have hS : tauStep kernel Assumptions.all l g s = some v := by
    rw [Assumptions.tauStep_all_eq_nil (by rw [hp]; decide) (hp.symm ▸ Flow.code_8444) rfl]
    unfold tauStep out
    rw [hf, hp, Flow.code_8444]
    let i : IntInstr := ⟨.add, .int .s 32, false, [some 7278], [.reg 7278, .imm 1]⟩
    have hl : (Op.int i).isLocal = true := rfl
    have hr : i.rule = some .threadInt := rfl
    change (match (if (Op.int i).isLocal then
        match execLocalA [] l g s (.int i) with
        | .ok t => Out.tau t | .error f => .ev (.ub f)
      else .ev (eventTmpl [] l g s (.int i))) with
      | .tau t => some t | .ev _ => none) = some v
    simp only [hl, ↓reduceIte, execLocalA_nil, execLocal, Op.rule, hr]
    have hOne : truncBits 32 (BitVec.ofInt 64 1) = BitVec.ofNat 64 1 := rfl
    have hExec : execInt l g s i = .ok v := by
      simp only [i, execInt, readValue, readBits, hReg', v, b32, DType.width,
        truncBits_ofNat hx (by decide), hOne, ← BitVec.ofNat_add, hInc, pure, Except.pure,
        bind, Except.bind]
    rw [hExec]
  have hVReg : readReg v 7278 = .ok (b32 y) := by
    simp [readReg, v, next, setReg, pure, Except.pure]
  have hV : tauStep kernel Assumptions.all l g v = some w := by
    rw [Assumptions.tauStep_all_eq_nil (by rw [hv]; decide) (hv.symm ▸ Flow.code_8445) rfl]
    unfold tauStep out
    rw [hvF, hv, Flow.code_8445]
    let i : IntInstr := ⟨(.setp .ne none), .int .b 32, false, [some 735], [.reg 7278, .imm (-1)]⟩
    have hl : (Op.int i).isLocal = true := rfl
    have hr : i.rule = some .threadInt := rfl
    change (match (if (Op.int i).isLocal then
        match execLocalA [] l g v (.int i) with
        | .ok t => Out.tau t | .error f => .ev (.ub f)
      else .ev (eventTmpl [] l g v (.int i))) with
      | .tau t => some t | .ev _ => none) = some w
    simp only [hl, ↓reduceIte, execLocalA_nil, execLocal, Op.rule, hr]
    have hLastBits : truncBits 32 (BitVec.ofInt 64 (-1)) =
        BitVec.ofNat 64 (2 ^ 32 - 1) := rfl
    have hCompare : compare .ne .b 32 (BitVec.ofNat 64 y) (BitVec.ofNat 64 (2 ^ 32 - 1)) =
        decide (steps ≠ 2) := by
      change decide (((BitVec.ofNat 64 y).toNat : Int) ≠ 4294967295) = _
      simp only [toNat_ofNat_lt (show y < 2 ^ 64 by omega)]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
    have hExec : execInt l g v i = .ok w := by
      simp only [i, execInt, readBits, hVReg, w, b32, DType.width, DType.kind?,
        Option.getD_some, truncBits_ofNat hy (by decide), hLastBits, hCompare,
        pure, Except.pure, bind, Except.bind]
    rw [hExec]
  have hWReg : readReg w 735 = .ok (.pred (decide (steps ≠ 2))) := by
    simp [readReg, w, next, setReg, pure, Except.pure]
  have hW : tauStep kernel Assumptions.all l g w =
      some (if steps = 2 then skip w else {w with pc := 8006}) := by
    rw [Assumptions.tauStep_all_eq_nil (by rw [hw]; decide) (hw.symm ▸ Flow.code_8446) rfl]
    unfold tauStep out
    rw [hwF, hw, Flow.code_8446]
    by_cases hEnd : steps = 2
    · simp [hEnd, guardHolds, hWReg, bind, Except.bind, pure, Except.pure]
    · have hr : (Op.bra 8006 false).rule = some .threadBranch := rfl
      have hl : (Op.bra 8006 false).isLocal = true := rfl
      simp [hEnd, guardHolds, hWReg, bind, Except.bind, pure, Except.pure,
        hl, hr, execLocalA_nil, execLocal, execBranch, hwF]
  have hR : w.regs 7278 = some (b32 y) := by simp [w, v, next, setReg]
  refine ⟨if steps = 2 then skip w else {w with pc := 8006}, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [run, hS, hV, hW, Option.bind_some]
  · split <;> simp [skip, hw]
  · split <;> exact hwF
  · split
    · exact Nat.zero_le _
    · exact le_rfl
  · split <;> exact hR


/-- The decoded loop test after one rescale pair decreases the live visit count. -/
theorem rescaleCounterStep {l : Launch} {g steps : Nat} {s : TState}
    (hPc : s.pc = 8444) (hFault : s.fault = none)
    (hReg : s.regs 7278 = some (b32 (2^32-steps))) (hLo : 2 ≤ steps) (hHi : steps ≤ 2^32) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      u.pc = (if steps = 2 then 8447 else 8006) ∧ u.fault = none ∧ u.sub ≤ s.sub ∧
      u.regs 7278 = some (b32 (2^32-(steps-1))) := by
  have hn : steps ≠ 1 := by omega
  simpa only [nextRescaleSteps, hn, ↓reduceIte] using
    rescaleCounterRun ⟨hPc, hFault, hReg⟩ (by omega) hHi

/-- From a rescale loop head, count its returning and terminal events without using
termination or memory consistency. Each taken backedge strictly decreases the rank. -/
theorem cutCorrectionRescale {l : Launch} {g cutoff steps : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hPc : s.pc = 8006) (hSub : s.sub ≤ 3) (hLo : 2 ≤ steps) (hHi : steps ≤ 2 ^ 32)
    (hReg : s.regs 7278 = some (b32 (2 ^ 32 - steps))) (hCut : 8447 ≤ cutoff)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    countedUntil cutoff visits ≤ 2194 * (steps - 1) ∨
    ∃ u rest tail, u.pc = 8447 ∧ u.sub ≤ 3 ∧ u.fault = none ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      countedUntil cutoff visits ≤ 2194 * (steps - 1) + countedUntil cutoff tail := by
  induction steps using Nat.strong_induction_on generalizing s events visits with
  | h steps ih =>
    obtain hBound | ⟨u, es, vs, hU, hF, hUSub, hKeep, hUWalk, hSplit⟩ :=
      cutCorrectionLinear 3 hPc hSub (by change 8444 ≤ cutoff; omega) hw
    · have hb : countedUntil cutoff visits ≤ 2194 := hBound
      exact .inl (by omega)
    · have hu : u.pc = 8444 := by simpa [correctionLinearRegion] using hU
      have hKeep' : u.regs 7278 = some (b32 (2 ^ 32 - steps)) := hKeep.trans hReg
      obtain ⟨v, hRun, hv, hVF, hVS, hR⟩ :=
        rescaleCounterRun (l := l) (g := g) ⟨hu, hF, hKeep'⟩ (by omega) hHi
      have hNoWrap : steps ≠ 1 := by omega
      simp only [nextRescaleSteps, hNoWrap, ↓reduceIte] at hR
      have hVSub := hVS.trans hUSub
      obtain hNil | ⟨post, _, hLater, hVWalk⟩ := advanceWalkLocals hRun hUWalk
      · subst es
        have hZ := zeroCountNoEvents hUWalk cutoff
        change countedUntil cutoff visits ≤ 2194 + countedUntil cutoff vs at hSplit
        exact .inl (by omega)
      · have hCount := hLater cutoff
        change countedUntil cutoff visits ≤ 2194 + countedUntil cutoff vs at hSplit
        by_cases hEnd : steps = 2
        · simp only [hEnd, ↓reduceIte] at hv
          exact .inr ⟨v, es, post, hv, hVSub, hVF, hVWalk, by omega⟩
        · simp only [hEnd, ↓reduceIte] at hv
          obtain hB | ⟨a, rs, ts, ha, haSub, haF, haW, haB⟩ :=
            ih (steps - 1) (by omega) hv hVSub (by omega) (by omega) hR hVWalk
          · exact .inl (by omega)
          · exact .inr ⟨a, rs, ts, ha, haSub, haF, haW, by omega⟩


private theorem rescaleSeedTau {l : Launch} {g : Nat} {s u : TState}
    (hPc : s.pc = 8005) (ht : Tau kernel Assumptions.all l g s u) :
    ∃ steps, 1 ≤ steps ∧ steps ≤ 2 ^ 32 ∧ u.pc = 8006 ∧ u.sub = s.sub ∧
      u.regs 7278 = some (b32 (2 ^ 32 - steps)) := by
  have hf : s.fault = none := by
    cases h : s.fault
    · rfl
    · simp [Tau, out, h] at ht
  have ht' := tauStep_iff.mpr ht
  rw [Assumptions.tauStep_all_eq_nil (by rw [hPc]; decide) (hPc.symm ▸ Flow.code_8005) rfl] at ht'
  have hCore : out kernel [] l g s = .tau u := tauStep_iff.mp ht'
  clear ht ht'
  have ht := hCore
  clear hCore
  have hCode := hPc.symm ▸ Flow.code_8005
  simp only [out, hf, hCode] at ht
  let i : IntInstr := ⟨.neg, .int .s 32, false, [some 7278], [.reg 1636]⟩
  have hl : (Op.int i).isLocal = true := rfl
  have hr : i.rule = some .threadInt := rfl
  change (if (Op.int i).isLocal then
      match execLocalA [] l g s (.int i) with
      | .ok t => Out.tau t | .error f => .ev (.ub f)
    else .ev (eventTmpl [] l g s (.int i))) = .tau u at ht
  simp only [hl, ↓reduceIte, execLocalA_nil, execLocal, Op.rule, hr] at ht
  rw [show execInt l g s i =
      ((readBits l g s 32 (.reg 1636)).map (fun x =>
        next (setReg s 7278 (.bits 32 (truncBits 32 (-x)))))) by
    simp only [i, execInt, DType.width]
    cases readBits l g s 32 (.reg 1636) <;> rfl] at ht
  cases hb : readBits l g s 32 (.reg 1636) with
  | error f => simp only [hb, Except.map, reduceCtorEq] at ht
  | ok x =>
    simp only [hb, Except.map, Out.tau.injEq] at ht
    subst u
    have hX : (-x).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    let steps := 2 ^ 32 - (-x).toNat % 2 ^ 32
    have hEq : 2 ^ 32 - steps = (-x).toNat % 2 ^ 32 := by dsimp [steps]; omega
    refine ⟨steps, by dsimp [steps]; omega, by dsimp [steps]; omega, ?_, rfl, ?_⟩
    · simp [next, setReg, hPc]
    · simp only [next, setReg, Function.update_self, b32, truncBits]
      rw [hEq]

private theorem cutRescaleAfterSeed {l : Launch} {g cutoff steps : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hPc : s.pc = 8006) (hSub : s.sub ≤ 3) (hLo : 1 ≤ steps) (hHi : steps ≤ 2 ^ 32)
    (hReg : s.regs 7278 = some (b32 (2 ^ 32 - steps))) (hCut : 8447 ≤ cutoff)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    countedUntil cutoff visits ≤ 2194 * 2 ^ 32 ∨
    ∃ u rest tail, u.pc = 8447 ∧ u.sub ≤ 3 ∧ u.fault = none ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      countedUntil cutoff visits ≤ 2194 * 2 ^ 32 + countedUntil cutoff tail := by
  by_cases hOne : steps = 1
  · subst steps
    obtain h | ⟨t, rest, tail, ht, hf, hS, hKeep, hw', hB⟩ :=
      cutCorrectionLinear 3 (cutoff := cutoff) hPc hSub (by change 8444 ≤ cutoff; omega) hw
    · have h' : countedUntil cutoff visits ≤ 2194 := h
      exact .inl (by omega)
    have ht' : t.pc = 8444 := List.mem_singleton.mp ht
    obtain ⟨u, hRun, hu, _, hUS, hReg'⟩ :=
      rescaleCounterRun (l := l) (g := g) ⟨ht', hf, hKeep.trans hReg⟩ (by decide) (by decide)
    have hu' : u.pc = 8006 := hu
    have hS' := hUS.trans hS
    have hB' : countedUntil cutoff visits ≤ 2194 + countedUntil cutoff tail := hB
    rcases advanceWalkLocals hRun hw' with hNil | ⟨vs, _, hCount, huW⟩
    · subst rest
      have hz := zeroCountNoEvents hw' cutoff
      exact .inl (by omega)
    · have hCount' := hCount cutoff
      rcases cutCorrectionRescale (steps := 2 ^ 32) hu' hS' (by decide) le_rfl hReg'
          hCut huW with hx | ⟨v, rest', tail', hv, hvS, hvF, hvW, hvB⟩
      · exact .inl (by omega)
      · exact .inr ⟨v, rest', tail', hv, hvS, hvF, hvW, by omega⟩
  · rcases cutCorrectionRescale hPc hSub (by omega) hHi hReg
      hCut hw with h | ⟨u, rest, tail, hu, hS, hf, hw, hB⟩
    · exact .inl (by omega)
    · exact .inr ⟨u, rest, tail, hu, hS, hf, hw, by omega⟩

/-- The actual counter initializer produces a 32-bit word. The cut covers any prefix
from its PC, including the terminal fault or the full finite rescale budget. -/
theorem cutCorrectionRescaleSeed {l : Launch} {g cutoff : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hPc : s.pc = 8005) (hSub : s.sub ≤ 3) (hCut : 8447 ≤ cutoff)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    countedUntil cutoff visits ≤ 2194 * 2 ^ 32 ∨
    ∃ u rest tail, u.pc = 8447 ∧ u.sub ≤ 3 ∧ u.fault = none ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      countedUntil cutoff visits ≤ 2194 * 2 ^ 32 + countedUntil cutoff tail := by
  have hIn : s.pc < cutoff := by omega
  cases hw with
  | stop => exact .inl (by simp [countedUntil])
  | tau ht hw' =>
    obtain ⟨steps, hLo, hHi, hp, hS, hReg⟩ := rescaleSeedTau hPc ht
    rw [countedCorrectionCons hIn none]
    simp only [Option.map_none, Option.getD_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact cutRescaleAfterSeed hp (hS ▸ hSub) hLo hHi hReg hCut hw'
  | ev he _ =>
    obtain ⟨ins, hc, hl, _⟩ := estep_event_source he
    rw [hPc, Flow.code_8005] at hc
    obtain rfl := Option.some.inj hc
    cases hl
  | @last s e he =>
    apply Or.inl
    rw [countedCorrectionCons hIn (some e)]
    simp only [countedUntil, List.takeWhile_nil, List.filterMap_nil, List.countP_nil, Nat.zero_add]
    split <;> decide

end
end PTX.Kernels.TmlFa4Fwd.Correction
