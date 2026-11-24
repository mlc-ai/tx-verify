-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Run
public import Lemmas.Flow.Scalars
public import Kernels.TmlFa4Fwd.Flow.Code.Part006
public import Kernels.TmlFa4Fwd.Flow.Sites
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
noncomputable section

/-- The value in the shift register after `n` bodies, starting at 2. -/
def shiftWord (n : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ (n + 1))

/-- The PTX's 32-bit shift does not wrap in any of the first 30 bodies. -/
theorem shiftWord_step {n : Nat} (h : n < 30) :
    truncBits 32 (shiftWord n <<< (1 : Nat)) = shiftWord (n + 1) := by
  have h₁ : 2 ^ (n + 1) < (2 : Nat) ^ 64 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have h₂ : 2 ^ (n + 1 + 1) < (2 : Nat) ^ 64 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have h₃ : 2 ^ (n + 1 + 1) < (2 : Nat) ^ 32 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [shiftWord, truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt h₁, ← Nat.pow_succ, Nat.mod_eq_of_lt h₂, Nat.mod_eq_of_lt h₃,
    Nat.mod_eq_of_lt h₂]

private theorem intStep {k : Kernel} {l : Launch} {g : Nat} {t u : TState}
    {i : IntInstr} (hf : t.fault = none) (hc : k.code[t.pc]? = some ⟨none, .int i⟩)
    (hl : (Op.int i).isLocal = true) (hr : i.rule = some .threadInt)
    (he : execInt l g t i = .ok u) :
    tauStep k [] l g t = some u := by
  have h : execLocalA [] l g t (.int i) = .ok u := by
    change execLocal l g t (.int i) = .ok u
    unfold execLocal
    rw [show (Op.int i).rule = some .threadInt from hr]
    exact he
  simp only [tauStep, out, hf, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, h]

/-- Register and program-counter effect of one complete pass through the frozen loop. -/
theorem shiftLoop_body (L : Launch) (g : Nat) (t : TState) (n : Nat)
    (counter limit : BitVec 64) (hn : n < 30)
    (hpc : t.pc = Flow.localLoop_0_entry) (hf : t.fault = none)
    (hsub : t.sub = 0) (hacc : t.acc = [])
    (hs : t.regs 7171 = some (.bits 32 (shiftWord n)))
    (hc : t.regs 1059 = some (.bits 16 counter))
    (hl : t.regs 1798 = some (.bits 32 limit)) :
    let take := decide ((shiftWord (n + 1)).toNat < (truncBits 32 limit).toNat)
    let u := setReg (setReg (setReg t 7171 (.bits 32 (shiftWord (n + 1))))
      1059 (.bits 16 (truncBits 16 (truncBits 16 counter + 1)))) 106 (.pred take)
    run Decoded.kernel [] L g 4 t = some
      { u with pc := if take then Flow.localLoop_0_entry else Flow.localLoop_0_exit } := by
  have hword : truncBits 32 (shiftWord n) = shiftWord n := by
    apply Proof.truncBits_ofNat
    · exact Nat.pow_lt_pow_right (by decide) (by omega)
    · decide
  have hword' : truncBits 32 (shiftWord (n + 1)) = shiftWord (n + 1) := by
    apply Proof.truncBits_ofNat
    · exact Nat.pow_lt_pow_right (by decide) (by omega)
    · decide
  let sh := shiftWord (n + 1)
  let ctr := truncBits 16 (truncBits 16 counter + 1)
  let pick := decide (sh.toNat < (truncBits 32 limit).toNat)
  let t1 := next (setReg t 7171 (.bits 32 sh))
  let t2 := next (setReg t1 1059 (.bits 16 ctr))
  let t3 := next (setReg t2 106 (.pred pick))
  let t4 := { t3 with pc := if pick then Flow.localLoop_0_entry else Flow.localLoop_0_exit }
  have hf1 : t1.fault = none := hf
  have hf2 : t2.fault = none := hf
  have hf3 : t3.fault = none := hf
  have hp1 : t1.pc = 399 := by change t.pc + 1 = 399; rw [hpc]
  have hp2 : t2.pc = 400 := by change t1.pc + 1 = 400; rw [hp1]
  have hp3 : t3.pc = Flow.localLoop_0_backedge := by change t2.pc + 1 = 401; rw [hp2]
  have h1 : tauStep Decoded.kernel [] L g t = some t1 := by
    have he : execInt L g t ⟨.shl, .int .b 32, false, [some 7171], [.reg 7171, .imm 1]⟩ =
        .ok t1 := by
      simp only [execInt, DType.width, readBits, readReg, hs, bind, Except.bind, pure, Except.pure,
        hword]
      change (Except.ok (next (setReg t 7171 (.bits 32
        (truncBits 32 (shiftWord n <<< (1 : Nat)))))) : Exec TState) = .ok t1
      rw [shiftWord_step hn]
    exact intStep hf (by rw [hpc]; exact Flow.code_398) rfl rfl he
  have h2 : tauStep Decoded.kernel [] L g t1 = some t2 := by
    have hctr : t1.regs 1059 = some (.bits 16 counter) := by simpa [t1, next, setReg] using hc
    have he : execInt L g t1 ⟨.add, .int .s 16, false, [some 1059], [.reg 1059, .imm 1]⟩ =
        .ok t2 := by
      simp only [execInt, DType.width, readValue, readReg, hctr, bind, Except.bind,
        pure, Except.pure, readBits]
      rfl
    exact intStep hf1 (by rw [hp1]; exact Flow.code_399) rfl rfl he
  have h3 : tauStep Decoded.kernel [] L g t2 = some t3 := by
    have hshift : t2.regs 7171 = some (.bits 32 sh) := by simp [t2, t1, next, setReg]
    have hlimit : t2.regs 1798 = some (.bits 32 limit) := by
      simpa [t2, t1, next, setReg] using hl
    have he : execInt L g t2
        ⟨.setp .lt none, .int .u 32, false, [some 106], [.reg 7171, .reg 1798]⟩ = .ok t3 := by
      simp only [execInt, DType.width, readBits, readReg, hshift, hlimit, bind, Except.bind,
        pure, Except.pure]
      change (Except.ok (next (setReg t2 106
        (.pred (compare .lt .u 32 (truncBits 32 sh) (truncBits 32 limit))))) :
          Exec TState) = .ok t3
      rw [hword']
      simp [compare, t3, pick, sh]
    exact intStep hf2 (by rw [hp2]; exact Flow.code_400) rfl rfl he
  have h4 : tauStep Decoded.kernel [] L g t3 = some t4 := by
    have hreg : t3.regs 106 = some (.pred pick) := by simp [t3, next, setReg]
    unfold tauStep out
    rw [hf3, hp3, Flow.code_401]
    by_cases hpick : pick = true
    · simp [guardHolds, readReg, hreg, hpick, bind, Except.bind, pure, Except.pure,
        Op.isLocal, execLocalA, execLocalRule, execLocal, Op.rule, execBranch, t4]
    · have hfalse : pick = false := Bool.eq_false_of_not_eq_true hpick
      have hex : t3.pc + 1 = Flow.localLoop_0_exit := by rw [hp3]
      have hs3 : t3.sub = 0 := hsub
      have ha3 : t3.acc = [] := hacc
      simp [guardHolds, readReg, hreg, hfalse, bind, Except.bind, pure, Except.pure,
        t4, skip, hex, hs3, ha3]
  have hh : run Decoded.kernel [] L g 4 t = some t4 := by
    simp only [run, h1, h2, h3, h4, Option.bind_some]
  simpa only [t1, t2, t3, t4, sh, ctr, pick, next, setReg] using hh

/-- The back edge tests the shifted word against an unsigned limit. The signed-negative
entry guard bounds that limit by 2^31. The first failed test therefore comes within 30
bodies, and every earlier test takes the back edge. -/
theorem shiftLoop_first_exit (limit : Nat) (hl : limit ≤ 2 ^ 31) :
    ∃ n, 1 ≤ n ∧ n ≤ 30 ∧ limit ≤ (shiftWord n).toNat ∧
      ∀ i, 1 ≤ i → i < n → (shiftWord i).toNat < limit := by
  let P := fun n => 1 ≤ n ∧ limit ≤ (shiftWord n).toNat
  have h₃₀ : P 30 := ⟨by decide, hl⟩
  have hex : ∃ n, P n := ⟨30, h₃₀⟩
  have hs := Nat.find_spec hex
  refine ⟨Nat.find hex, hs.1, Nat.find_min' hex h₃₀, hs.2, ?_⟩
  intro i hp hi
  exact Nat.lt_of_not_ge fun h => Nat.find_min hex hi ⟨hp, h⟩


/-- From the initialized loop entry, the four decoded local instructions can run at most
30 times before reaching the exit. -/
theorem shiftLoop_terminates (L : Launch) (g : Nat) (t : TState) (counter limit : BitVec 64)
    (hpc : t.pc = Flow.localLoop_0_entry) (hf : t.fault = none)
    (hsub : t.sub = 0) (hacc : t.acc = [])
    (hs : t.regs 7171 = some (.bits 32 (shiftWord 0)))
    (hc : t.regs 1059 = some (.bits 16 counter))
    (hl : t.regs 1798 = some (.bits 32 limit)) (hb : (truncBits 32 limit).toNat ≤ 2 ^ 31) :
    ∃ steps ≤ 120, ∃ u, run Decoded.kernel [] L g steps t = some u ∧
      u.pc = Flow.localLoop_0_exit := by
  obtain ⟨n, hpos, hmax, hlast, hprev⟩ := shiftLoop_first_exit _ hb
  have prefixRun : ∀ i < n, ∃ u c, run Decoded.kernel [] L g (4 * i) t = some u ∧
      u.pc = Flow.localLoop_0_entry ∧ u.fault = none ∧ u.sub = 0 ∧ u.acc = [] ∧
      u.regs 7171 = some (.bits 32 (shiftWord i)) ∧ u.regs 1059 = some (.bits 16 c) ∧
      u.regs 1798 = some (.bits 32 limit) := by
    intro i hi
    induction i with
    | zero => exact ⟨t, counter, rfl, hpc, hf, hsub, hacc, hs, hc, hl⟩
    | succ i ih =>
      obtain ⟨u, c, hu, hp, hfu, hsu, hau, hshift, hcounter, hlimit⟩ := ih (by omega)
      have hlt := hprev (i + 1) (by omega) hi
      have hstep := shiftLoop_body L g u i c limit (by omega) hp hfu hsu hau
        hshift hcounter hlimit
      simp only [decide_eq_true hlt, ↓reduceIte] at hstep
      let c' := truncBits 16 (truncBits 16 c + 1)
      let u' := setReg (setReg (setReg u 7171 (.bits 32 (shiftWord (i + 1))))
        1059 (.bits 16 c')) 106 (.pred true)
      refine ⟨{ u' with pc := Flow.localLoop_0_entry }, c', ?_, rfl, hfu, hsu, hau, ?_, ?_, ?_⟩
      · rw [Nat.mul_succ]
        exact run_comp hu hstep
      · simp [u', setReg]
      · simp [u', setReg]
      · simpa [u', setReg] using hlimit
  obtain ⟨u, c, hu, hp, hfu, hsu, hau, hshift, hcounter, hlimit⟩ :=
    prefixRun (n - 1) (by omega)
  have hstep := shiftLoop_body L g u (n - 1) c limit (by omega) hp hfu hsu hau
    hshift hcounter hlimit
  have hn : n - 1 + 1 = n := by omega
  have hgt : ¬ (shiftWord n).toNat < (truncBits 32 limit).toNat := Nat.not_lt.mpr hlast
  simp only [hn, decide_eq_false hgt, Bool.false_eq_true, ↓reduceIte] at hstep
  exact ⟨4 * (n - 1) + 4, by omega, _, run_comp hu hstep, rfl⟩

end
end PTX.Kernels.TmlFa4Fwd
