-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Flow.Code.Part078
public import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- The frozen signed subtraction and negation establish a 32-bit rank word for each loop. -/
def scoreInitPc : ScoreLoop → Nat
  | .biased => 5025
  | .plain => 6657

private theorem counterBits {s u : TState} {r : Nat} (v : BitVec 64)
    (h : next (setReg s r (.bits 32 (truncBits 32 v))) = u) :
    u.pc = s.pc + 1 ∧ u.sub = s.sub ∧
      ∃ w < 2 ^ 32, u.regs r = some (b32 w) := by
  subst u
  let bits := truncBits 32 v
  have hNat : bits.toNat < 2 ^ 32 := by
    simp only [bits, truncBits, BitVec.toNat_ofNat]
    exact (Nat.mod_le _ _).trans_lt (Nat.mod_lt _ (by decide))
  have hBits : BitVec.ofNat 64 bits.toNat = bits := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bits.isLt]
  exact ⟨rfl, rfl, bits.toNat, hNat, by simp [next, setReg, b32, hBits, bits]⟩

private theorem scoreInitFirst (loop : ScoreLoop) {l : Launch} {g : Nat} {s u : TState}
    (hp : s.pc = scoreInitPc loop)
    (hBias : loop = .biased → ∃ v, s.regs 1359 = some (.bits 32 v))
    (ht : Tau kernel Assumptions.all l g s u) :
    u.pc = s.pc + 1 ∧ u.sub = s.sub ∧
      ∃ w < 2 ^ 32, u.regs (scoreLoopSite loop).word = some (b32 w) := by
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hp]; cases loop <;> decide
  obtain ⟨i, hc, hF, hExec⟩ := tauScoreSource ht
  cases loop
  · rw [show s.pc = 5025 from hp, Flow.code_5025] at hc
    obtain rfl := (Option.some.inj hc).symm
    rcases hExec with ⟨_, hg⟩ | ⟨_, _, he⟩
    · cases hg
    · rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl,
        execLocalA_nil, execLocal_int rfl] at he
      obtain ⟨a, ha⟩ := hBias rfl
      have hA : readBits l g s 32 (.reg 1359) = .ok (truncBits 32 a) := by
        simp only [readBits, readReg, ha, bind, Except.bind, pure, Except.pure]
      simp only [execInt, DType.width, readValue, readReg, ha, hA, bind,
        Except.bind, pure, Except.pure] at he
      cases hB : readBits l g s 32 (.reg 1226) with
      | error f => simp [hB] at he
      | ok b =>
        simp only [hB, Except.ok.injEq] at he
        exact counterBits _ he
  · rw [show s.pc = 6657 from hp, Flow.code_6657] at hc
    obtain rfl := (Option.some.inj hc).symm
    rcases hExec with ⟨_, hg⟩ | ⟨_, _, he⟩
    · cases hg
    · rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl,
        execLocalA_nil, execLocal_int rfl] at he
      change (readBits l g s 32 (.reg 1491) >>= fun a =>
        Except.ok (next (setReg s 7254 (.bits 32 (truncBits 32 (-a)))))) = .ok u at he
      cases hA : readBits l g s 32 (.reg 1491) with
      | error f => simp [hA, bind, Except.bind] at he
      | ok a =>
        simp only [hA, bind, Except.bind, Except.ok.injEq] at he
        exact counterBits (-a) he

private theorem scoreInitInstruction (loop : ScoreLoop) {s : TState} {i : Instr}
    (hLo : scoreInitPc loop + 1 ≤ s.pc) (hHi : s.pc < (scoreLoopSite loop).head)
    (hc : kernel.code[s.pc]? = some i) :
    i.op.isLocal = true ∧ nextPc i.op s.pc = s.pc + 1 ∧
      (scoreLoopSite loop).word ∉ writesRegs i.op ∧ s.pc ∉ Assumptions.swExp2Sites ∧
      (∀ index targets uni, i.op ≠ .brx index targets uni) := by
  cases loop with
  | biased =>
    simp only [scoreInitPc, scoreLoopSite] at hLo hHi ⊢
    generalize hp : s.pc = pc at hc hLo hHi ⊢
    interval_cases pc
    all_goals
      first
      | rw [Flow.code_5026] at hc
      | rw [Flow.code_5027] at hc
      | rw [Flow.code_5028] at hc
      | rw [Flow.code_5029] at hc
      | rw [Flow.code_5030] at hc
      | rw [Flow.code_5031] at hc
    all_goals
      obtain rfl := (Option.some.inj hc).symm
      refine ⟨rfl, rfl, by decide, by decide, ?_⟩
      intro idx targets uni h
      cases h
  | plain =>
    simp only [scoreInitPc, scoreLoopSite] at hLo hHi ⊢
    generalize hp : s.pc = pc at hc hLo hHi ⊢
    interval_cases pc
    all_goals
      first
      | rw [Flow.code_6658] at hc
      | rw [Flow.code_6659] at hc
      | rw [Flow.code_6660] at hc
    all_goals
      obtain rfl := (Option.some.inj hc).symm
      refine ⟨rfl, rfl, by decide, by decide, ?_⟩
      intro idx targets uni h
      cases h

private theorem counterInitLocals (loop : ScoreLoop) {l : Launch} {g n : Nat} {s u : TState}
    (hLo : scoreInitPc loop + 1 ≤ s.pc) (hHi : s.pc + n ≤ (scoreLoopSite loop).head)
    (hr : run kernel Assumptions.all l g n s = some u) :
    u.pc = s.pc + n ∧ u.sub ≤ s.sub ∧
      u.regs (scoreLoopSite loop).word = s.regs (scoreLoopSite loop).word := by
  induction n generalizing s with
  | zero =>
    obtain rfl := Option.some.inj hr
    exact ⟨rfl, le_rfl, rfl⟩
  | succ n ih =>
    simp only [run] at hr
    cases hTau : tauStep kernel Assumptions.all l g s with
    | none => simp [hTau] at hr
    | some t =>
      simp only [hTau, Option.bind_some] at hr
      obtain ⟨i, hc, _, hExec⟩ := tauScoreSource (tauStep_iff.mp hTau)
      have ⟨hLoc, hPc, hR, hOff, hNoBrx⟩ := scoreInitInstruction loop hLo (by omega) hc
      have hFrame : t.pc = s.pc + 1 ∧ t.sub ≤ s.sub ∧
          t.regs (scoreLoopSite loop).word = s.regs (scoreLoopSite loop).word := by
        rcases hExec with ⟨rfl, _⟩ | ⟨_, _, he⟩
        · exact ⟨rfl, Nat.zero_le _, rfl⟩
        · have h := (scoreExecLocal he).resolve_right (fun ⟨_, hs, _, _⟩ => hOff hs)
          have hTarget : ¬ BrxTarget i.op t.pc := by
            cases hOp : i.op <;> simp only [BrxTarget, not_false_eq_true]
            exact (hNoBrx _ _ _ hOp).elim
          exact ⟨(h.pc.resolve_right hTarget).trans hPc, h.sub.le, h.regs _ hR⟩
      obtain ⟨hU, huS, huR⟩ := ih (by omega) (by omega) hr
      exact ⟨by omega, huS.trans hFrame.2.1, huR.trans hFrame.2.2⟩

/-- A successful traversal of the preheader establishes the starting rank for the actual loop. -/
theorem scoreLoopInitialized (loop : ScoreLoop) {l : Launch} {g : Nat} {s u : TState}
    (hPc : s.pc = scoreInitPc loop) (hSub : s.sub ≤ 3)
    (hBias : loop = .biased → ∃ v, s.regs 1359 = some (.bits 32 v))
    (hr : run kernel Assumptions.all l g ((scoreLoopSite loop).head - scoreInitPc loop)
      s = some u) :
    u.pc = (scoreLoopSite loop).head ∧ u.sub ≤ 3 ∧
      ∃ w < 2 ^ 32, u.regs (scoreLoopSite loop).word = some (b32 w) := by
  let n := (scoreLoopSite loop).head - (scoreInitPc loop + 1)
  have hn : (scoreLoopSite loop).head - scoreInitPc loop = n + 1 := by cases loop <;> decide
  rw [hn, run] at hr
  cases hT : tauStep kernel Assumptions.all l g s with
  | none => simp [hT] at hr
  | some t =>
    simp only [hT, Option.bind_some] at hr
    obtain ⟨ht, hS, w, hw, hW⟩ := scoreInitFirst loop hPc hBias (tauStep_iff.mp hT)
    have hEnd : t.pc + n = (scoreLoopSite loop).head := by rw [ht, hPc]; cases loop <;> decide
    obtain ⟨hu, huS, huW⟩ := counterInitLocals loop (by omega) hEnd.le hr
    exact ⟨hu.trans hEnd, huS.trans (hS.symm ▸ hSub), w, hw, huW.trans hW⟩

private theorem scoreInitLocal (loop : ScoreLoop) {s : TState} {i : Instr}
    (hLo : scoreInitPc loop ≤ s.pc) (hHi : s.pc < (scoreLoopSite loop).head)
    (hc : kernel.code[s.pc]? = some i) : i.op.isLocal = true := by
  by_cases he : s.pc = scoreInitPc loop
  · cases loop
    · rw [show s.pc = 5025 from he, Flow.code_5025] at hc
      obtain rfl := (Option.some.inj hc).symm
      rfl
    · rw [show s.pc = 6657 from he, Flow.code_6657] at hc
      obtain rfl := (Option.some.inj hc).symm
      rfl
  · exact (scoreInitInstruction loop (by omega) hHi hc).1

private theorem scoreInitNext (loop : ScoreLoop) {l : Launch} {g : Nat} {s u : TState}
    (hLo : scoreInitPc loop ≤ s.pc) (hHi : s.pc < (scoreLoopSite loop).head)
    (hBias : s.pc = scoreInitPc loop → loop = .biased → ∃ v, s.regs 1359 = some (.bits 32 v))
    (ht : Tau kernel Assumptions.all l g s u) : u.pc = s.pc + 1 := by
  by_cases he : s.pc = scoreInitPc loop
  · exact (scoreInitFirst loop he (hBias he) ht).1
  · have hRun : run kernel Assumptions.all l g 1 s = some u := by
      simp only [run, tauStep_iff.mpr ht, Option.bind_some]
    exact (counterInitLocals loop (by omega) (by omega) hRun).1

/-- A later observed event forces traversal of the silent score-loop preheader. -/
theorem scoreRunToHeadBefore {l : Launch} {g : Nat} (loop : ScoreLoop)
    {s : TState} {es : List Event} {vs : List Visit} {target : Event}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hLo : scoreInitPc loop ≤ s.pc) (hHi : s.pc ≤ (scoreLoopSite loop).head)
    (hBias : s.pc = scoreInitPc loop → loop = .biased → ∃ v, s.regs 1359 = some (.bits 32 v))
    (hFound : target ∈ es) (hTarget : (scoreLoopSite loop).head ≤ target.pc) :
    ∃ u tail, run kernel Assumptions.all l g ((scoreLoopSite loop).head - s.pc) s = some u ∧
      Walk kernel Assumptions.all l g u es tail := by
  induction hw with
  | stop => cases hFound
  | @tau s t es vs ht hw ih =>
    by_cases hEnd : s.pc = (scoreLoopSite loop).head
    · exact ⟨s, _, by rw [hEnd, Nat.sub_self]; rfl, .tau ht hw⟩
    have hNext := scoreInitNext loop hLo (by omega) hBias ht
    obtain ⟨u, tail, hRun, hWalk⟩ :=
      ih (by omega) (by omega) (fun h _ => False.elim (by omega)) hFound
    have hSteps : (scoreLoopSite loop).head - s.pc =
        ((scoreLoopSite loop).head - t.pc) + 1 := by omega
    refine ⟨u, tail, ?_, hWalk⟩
    rw [hSteps, run, tauStep_iff.mpr ht, Option.bind_some]
    exact hRun
  | @ev s t e es vs he hw ih =>
    by_cases hEnd : s.pc = (scoreLoopSite loop).head
    · exact ⟨s, _, by rw [hEnd, Nat.sub_self]; rfl, .ev he hw⟩
    obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
    rw [scoreInitLocal loop hLo (by omega) hc] at hLocal
    cases hLocal
  | @last s e he =>
    have hEqual := List.mem_singleton.mp hFound
    have hSame := (estep_source_pc he).symm.trans (congrArg Event.pc hEqual.symm)
    have hEnd : s.pc = (scoreLoopSite loop).head := by omega
    exact ⟨s, _, by rw [hEnd, Nat.sub_self]; rfl, .last he⟩

/-- The actual ordinary preheader starts the loop with the negated clipped block count. -/
theorem plainLoopInitializedCount {l : Launch} {g count : Nat} {s u : TState}
    (hPc : s.pc = 6657) (hSub : s.sub ≤ 3)
    (hCount : s.regs 1491 = some (b32 count)) (hLo : 0 < count) (hHi : count < 2^32)
    (hRun : run kernel Assumptions.all l g 4 s = some u) :
    u.pc = 6661 ∧ u.sub ≤ 3 ∧ u.regs 7254 = some (b32 (2^32-count)) := by
  rw [show 4 = 3+1 by decide, run] at hRun
  cases hNext : tauStep kernel Assumptions.all l g s with
  | none => simp only [hNext, Option.bind_none] at hRun; cases hRun
  | some t =>
    simp only [hNext, Option.bind_some] at hRun
    obtain ⟨i, hc, _, hExec⟩ := tauScoreSource (tauStep_iff.mp hNext)
    rw [hPc, Flow.code_6657] at hc
    obtain rfl := Option.some.inj hc.symm
    rcases hExec with ⟨_, hg⟩ | ⟨_, _, he⟩
    · cases hg
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; decide
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl,
      execLocalA_nil, execLocal_int rfl] at he
    change (readBits l g s 32 (.reg 1491) >>= fun a =>
      Except.ok (next (setReg s 7254 (.bits 32 (truncBits 32 (-a)))))) = .ok t at he
    have hRead := readBits_b32 (L := l) (g := g) hCount hHi
    have hNeg : truncBits 32 (-(BitVec.ofNat 64 count)) = BitVec.ofNat 64 (2^32-count) := by
      norm_bits
    simp only [hRead, bind, Except.bind, Except.ok.injEq, hNeg] at he
    subst t
    change run kernel Assumptions.all l g 3 (next (setReg s 7254 (b32 (2^32-count)))) =
      some u at hRun
    have hStart : (next (setReg s 7254 (b32 (2^32-count)))).pc = 6658 := by
      simpa only [next, setReg] using congrArg (·+1) hPc
    obtain ⟨hEnd, hSteps, hFrame⟩ := counterInitLocals .plain (by rw [hStart]; decide)
      (by rw [hStart]; decide) hRun
    exact ⟨hEnd.trans (by rw [hStart]), hSteps.trans hSub,
      hFrame.trans (by simp [scoreLoopSite, next, setReg])⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
