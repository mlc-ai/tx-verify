-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLoopRank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem prependLocalWalk {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g u es vs)
    (ht : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) :
    ∃ visits, Walk kernel Assumptions.all l g s es visits := by
  induction ht using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨vs, hw⟩
  | head ht _ ih =>
    obtain ⟨visits, hWalk⟩ := ih
    exact ⟨_, .tau ht hWalk⟩

theorem walkFromRun {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {o : Option TState} (h : Run kernel Assumptions.all l g s es o) :
    ∃ visits, Walk kernel Assumptions.all l g s es visits := by
  induction h with
  | nil t => exact ⟨[], .stop t⟩
  | step hTau he _ ih =>
    obtain ⟨visits, hw⟩ := ih
    exact prependLocalWalk (.ev he hw) hTau
  | last hTau he => exact prependLocalWalk (.last he) hTau

private theorem negCounterWord {l : Launch} {g : Nat} {s u : TState}
    (hs : s.pc = 2286) (ht : Tau kernel Assumptions.all l g s u) :
    u.pc = 2287 ∧ ∃ word, word < 2 ^ 32 ∧ u.regs 7204 = some (b32 word) := by
  unfold Tau at ht
  rw [out_eq_core (by omega) (by omega)] at ht
  let i : IntInstr :=
    { op := .neg, ty := .int .s 32, sat := false, dsts := [some 7204], srcs := [.reg 1189] }
  have hc : kernel.code[s.pc]? = some ⟨none, .int i⟩ := by rw [hs]; exact Flow.code_2286
  have hLoc : (Op.int i).isLocal = true := rfl
  have hExec : execLocalA [] l g s (.int i) =
      (readBits l g s 32 (.reg 1189) >>= fun x =>
        Except.ok (next (setReg s 7204 (.bits 32 (truncBits 32 (-x)))))) := rfl
  cases hFault : s.fault with
  | some f => simp [out, hFault] at ht
  | none =>
    simp only [out, hFault, hc, guardHolds, pure, Except.pure, hLoc, ↓reduceIte, hExec] at ht
    cases hRead : readBits l g s 32 (.reg 1189) with
    | error f => simp [hRead, bind, Except.bind] at ht
    | ok x =>
      simp [hRead, bind, Except.bind] at ht
      subst u
      let bits := truncBits 32 (-x)
      refine ⟨by simp [next, setReg, hs], bits.toNat, ?_, ?_⟩
      · simp only [bits, truncBits, BitVec.toNat_ofNat]
        have hMod : (-x).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
        exact (Nat.mod_le _ _).trans_lt hMod
      · have hBits : BitVec.ofNat 64 bits.toNat = bits := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bits.isLt]
        exact congrArg (fun v => some (Value.bits 32 v)) hBits.symm

private theorem counterEntryMoves {pc : Nat} (hLo : 2287 ≤ pc) (hHi : pc < 2291) :
    ∃ move, kernel.code[pc]? = some ⟨none, .move move⟩ ∧ 7204 ∉ writesRegs (.move move) := by
  interval_cases pc
  · exact ⟨_, Flow.code_2287, by decide⟩
  · exact ⟨_, Flow.code_2288, by decide⟩
  · exact ⟨_, Flow.code_2289, by decide⟩
  · exact ⟨_, Flow.code_2290, by decide⟩

private theorem enterAfterNeg {l : Launch} {g n : Nat} {s u : TState} (hLo : 2287 ≤ s.pc)
    (hHi : s.pc + n ≤ 2291) (h : run kernel Assumptions.all l g n s = some u) :
    u.pc = s.pc + n ∧ u.regs 7204 = s.regs 7204 := by
  induction n generalizing s with
  | zero =>
    obtain rfl := Option.some.inj h
    exact ⟨by simp, rfl⟩
  | succ n ih =>
    simp only [run] at h
    cases ht : tauStep kernel Assumptions.all l g s with
    | none => simp [ht] at h
    | some v =>
      rw [ht, Option.bind_some] at h
      have hTau : Tau kernel [] l g s v := by
        have hStep := tauStep_iff.mp ht
        unfold Tau at hStep ⊢
        rwa [← out_eq_core (by omega) (by omega)]
      obtain ⟨mv, hc, hRegs⟩ := counterEntryMoves hLo (by omega)
      have hKeep := tau_core_regs hc hTau hRegs
      have hPc : v.pc = s.pc + 1 := by
        rcases tau_core_frame hc hTau with rfl | hFrame
        · rfl
        · exact hFrame.pc.resolve_right id
      obtain ⟨hNext, hReg⟩ := ih (by omega) (by omega) h
      exact ⟨by omega, hReg.trans hKeep⟩

/-- Reaching the loop through the decoded five-step initialization establishes a
32-bit trip counter without interpreting the source trip register. -/
theorem initializedCounterWord {l : Launch} {g : Nat} {s u : TState}
    (hp : s.pc = 2286) (h : run kernel Assumptions.all l g 5 s = some u) :
    u.pc = 2291 ∧ ∃ word, word < 2 ^ 32 ∧ u.regs 7204 = some (b32 word) := by
  change (tauStep kernel Assumptions.all l g s).bind (run kernel Assumptions.all l g 4) =
    some u at h
  cases hs : tauStep kernel Assumptions.all l g s with
  | none => simp [hs] at h
  | some v =>
    rw [hs, Option.bind_some] at h
    obtain ⟨hPC, w, hW, hv⟩ := negCounterWord hp (tauStep_iff.mp hs)
    obtain ⟨hU, hKeep⟩ := enterAfterNeg hPC.ge (by omega) h
    exact ⟨by omega, w, hW, hKeep.trans hv⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
