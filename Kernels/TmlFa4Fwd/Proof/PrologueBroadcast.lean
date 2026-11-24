-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Flow.Code.Part000
public import Lemmas.Flow.Regs
public import Lemmas.Isa.Rule

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section

/-- Linear warp number in the CTA. -/
def warpIndex (l : Launch) (g : Nat) : Nat := g % l.block / 32

theorem warpIndex_lt {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m) (g : Nat) :
    warpIndex l g < 16 := by
  unfold warpIndex
  rw [hpre.block]
  have := Nat.mod_lt g (show 0 < 512 by decide)
  omega

private def idxOp (dst src : Nat) : Op :=
  .warp ⟨.shfl .idx, some (.int .b 32), [some dst], [.reg src, .imm 0, .imm 31], some (.imm (-1))⟩

/-- The template of a full-mask lane-zero broadcast. -/
def broadcastTemplate (t : TState) (dst : Nat) (src : Value) : Tmpl :=
  .shfl .idx src 0 31 (fun recv _ => next (setReg t dst recv))

private theorem idxOut {l : Launch} {g pc dst src x : Nat} {t : TState}
    (hb : l.block = 512) (hp : t.pc = pc) (hf : t.fault = none)
    (hr : t.regs src = some (b32 x)) (hc : kernel.code[pc]? = some ⟨none, idxOp dst src⟩) :
    out kernel [] l g t = .ev (broadcastTemplate t dst (b32 x)) := by
  unfold out
  rw [hp, hf, hc]
  have hl : (idxOp dst src).isLocal = false := rfl
  simp only [guardHolds, pure, Except.pure, hl, Bool.false_eq_true, ↓reduceIte]
  change Out.ev (shflTmpl l g t .idx dst none (.reg src) (.imm 0) (.imm 31) (.imm (-1))) = _
  simp [shflTmpl, broadcastTemplate, hb, readValue, readReg, hr, b32]
  rfl

private theorem evalLocal {l : Launch} {g pc : Nat} {t u : TState} {op : Op}
    (hp : t.pc = pc) (hf : t.fault = none) (hc : kernel.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (he : execLocal l g t op = .ok u) :
    tauStep kernel [] l g t = some u := by
  have he' : execLocalA [] l g t op = .ok u := he
  simp only [tauStep, out, hp, hf, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, he']

private theorem evalSReg {l : Launch} {g pc r n : Nat} {t : TState} {s : SReg}
    (hp : t.pc = pc) (hf : t.fault = none) (hw : s.width ≠ 1)
    (hr : sregValue l g s = some n) (hn : n < 2 ^ 32)
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.scalar, .int .u 32, [some r], [.sreg s]⟩⟩)
    (hl : (Op.move ⟨.scalar, .int .u 32, [some r], [.sreg s]⟩).isLocal = true)
    (hm : (MoveInstr.mk .scalar (.int .u 32) [some r] [.sreg s]).rule = some .threadMove) :
    tauStep kernel [] l g t = some (next (setReg t r (b32 n))) := by
  apply evalLocal hp hf hc hl
  rw [execLocal_move hm]
  simp [execMove, DType.width, Value.bytes, readValue, readBits, hw, hr, bind, Except.bind,
    pure, Except.pure, truncBits_ofNat hn (by decide), b32]

/-- PC 25 broadcasts the dynamic shared-memory base from lane 0. -/
theorem sharedBroadcastOut {l : Launch} {g : Nat} {t : TState}
    (hb : l.block = 512) (hp : t.pc = 25) (hf : t.fault = none)
    (hr : t.regs 1665 = some (b32 l.sharedBase)) :
    out kernel [] l g t = .ev (broadcastTemplate t 2535 (b32 l.sharedBase)) :=
  idxOut hb hp hf hr Flow.code_25

/-- The local instructions after the shared-base shuffle compute `tid.x / 32` in a 1D CTA. -/
theorem warpIndexLocalWithTid {A : List Assumption} [StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    (g : Nat) (t : TState) (hpc : t.pc = 26) (hf : t.fault = none) :
    ∃ u, run kernel A l g 8 t = some u ∧ u.pc = 34 ∧ u.fault = none ∧
      u.regs 1672 = some (b32 (warpIndex l g)) ∧ u.regs 1061 = some (b32 (g % l.block)) ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧
      ∀ r ∉ [1061, 1666, 1667, 1668, 1669, 1670, 1671, 1672], u.regs r = t.regs r := by
  let tid := g % l.block
  have ht : tid < 2 ^ 32 := by
    have hh : tid < l.block := Nat.mod_lt g (by rw [hpre.block]; decide)
    rw [hpre.block] at hh
    omega
  have hdim := sregValue_oneDim hpre.cluster.2.2 g
  have hdy := hdim.2.2.2.2.2.2.2.2.2.2 .y (by decide)
  have hdz := hdim.2.2.2.2.2.2.2.2.2.2 .z (by decide)
  let t1 := next (setReg t 1061 (b32 tid))
  let t2 := next (setReg t1 1666 (b32 0))
  let t3 := next (setReg t2 1667 (b32 0))
  let t4 := next (setReg t3 1668 (b32 l.block))
  let t5 := next (setReg t4 1669 (b32 1))
  let t6 := next (setReg t5 1670 (b32 0))
  let t7 := next (setReg t6 1671 (b32 tid))
  let t8 := next (setReg t7 1672 (b32 (warpIndex l g)))
  have h1 : tauStep kernel [] l g t = some t1 :=
    evalSReg (pc := 26) hpc hf (by decide) hdim.1 ht Flow.code_26 rfl rfl
  have h2 : tauStep kernel [] l g t1 = some t2 :=
    evalSReg (pc := 27) (t := t1) (by change t.pc + 1 = 27; rw [hpc]) hf (by decide) hdy.1
      (by decide) Flow.code_27 rfl rfl
  have h3 : tauStep kernel [] l g t2 = some t3 :=
    evalSReg (pc := 28) (t := t2) (by change t.pc + 2 = 28; rw [hpc]) hf (by decide) hdz.1
      (by decide) Flow.code_28 rfl rfl
  have hblock : l.block < 2 ^ 32 := by rw [hpre.block]; decide
  have h4 : tauStep kernel [] l g t3 = some t4 :=
    evalSReg (pc := 29) (t := t3) (by change t.pc + 3 = 29; rw [hpc]) hf (by decide) hdim.2.1
      hblock Flow.code_29 rfl rfl
  have h5 : tauStep kernel [] l g t4 = some t5 :=
    evalSReg (pc := 30) (t := t4) (by change t.pc + 4 = 30; rw [hpc]) hf (by decide) hdy.2.2.2.2.1
      (by decide) Flow.code_30 rfl rfl
  have h6 : tauStep kernel [] l g t5 = some t6 := by
    apply evalLocal (pc := 31) (t := t5) (by change t.pc + 5 = 31; rw [hpc]) hf Flow.code_31 rfl
    rw [execLocal_int rfl]
    have r1 : t5.regs 1669 = some (b32 1) := rfl
    have r2 : t5.regs 1667 = some (b32 0) := rfl
    have r3 : t5.regs 1666 = some (b32 0) := rfl
    simp only [execInt, DType.width, readBits, readReg, r1, r2, r3, bind, Except.bind,
      pure, Except.pure]
    rfl
  have h7 : tauStep kernel [] l g t6 = some t7 := by
    apply evalLocal (pc := 32) (t := t6) (by change t.pc + 6 = 32; rw [hpc]) hf Flow.code_32 rfl
    rw [execLocal_int rfl]
    have r1 : t6.regs 1670 = some (b32 0) := rfl
    have r2 : t6.regs 1668 = some (b32 l.block) := rfl
    have r3 : t6.regs 1061 = some (b32 tid) := rfl
    simp only [execInt, DType.width, readBits, readReg, r1, r2, r3, bind, Except.bind,
      pure, Except.pure, b32, truncBits_ofNat ht (by decide)]
    change Except.ok (next (setReg t6 1671 (.bits 32 (truncBits 32
      (0 * truncBits 32 (BitVec.ofNat 64 l.block) + BitVec.ofNat 64 tid))))) = _
    rw [zero_mul, zero_add, truncBits_ofNat ht (by decide)]
    rfl
  have h8 : tauStep kernel [] l g t7 = some t8 := by
    apply evalLocal (pc := 33) (t := t7) (by change t.pc + 7 = 33; rw [hpc]) hf Flow.code_33 rfl
    rw [execLocal_int rfl]
    have r1 : t7.regs 1671 = some (b32 tid) := rfl
    simp only [execInt, DType.width, readBits, readReg, r1, bind, Except.bind,
      pure, Except.pure, b32, truncBits_ofNat ht (by decide)]
    simp only [DType.kind?, show (some IType.u == some IType.s) = false by decide,
      Bool.false_eq_true, ↓reduceIte,
      show (truncBits 32 (BitVec.ofInt 64 5)).toNat = 5 by decide,
      show ¬(5 : Nat) ≥ 32 by decide]
    change Except.ok (next (setReg t7 1672 (.bits 32
      (BitVec.ofNat 64 tid >>> (5 : Nat))))) = _
    have hshr : BitVec.ofNat 64 tid >>> (5 : Nat) = BitVec.ofNat 64 (warpIndex l g) := by
      have hb64 : tid < 2 ^ 64 := lt_trans ht (by decide)
      have hw64 : warpIndex l g < 2 ^ 64 := lt_trans (warpIndex_lt hpre g) (by decide)
      apply BitVec.eq_of_toNat_eq
      change (BitVec.ofNat 64 tid).toNat >>> (5 : Nat) = (BitVec.ofNat 64 (warpIndex l g)).toNat
      rw [toNat_ofNat_lt hb64, toNat_ofNat_lt hw64, Nat.shiftRight_eq_div_pow]
      rfl
    rw [hshr]
    rfl
  refine ⟨t8, ?_, by change t.pc + 8 = 34; rw [hpc], hf, rfl, rfl, rfl, rfl, ?_⟩
  · have lift {s u : TState} {j : Nat} (hj : j < 8) (h : s.pc = t.pc + j)
        (hs : tauStep kernel [] l g s = some u) : tauStep kernel A l g s = some u :=
      startupTau (.inl (by omega)) hs
    have s1 := lift (j := 0) (by decide) rfl h1
    have s2 := lift (j := 1) (by decide) rfl h2
    have s3 := lift (j := 2) (by decide) rfl h3
    have s4 := lift (j := 3) (by decide) rfl h4
    have s5 := lift (j := 4) (by decide) rfl h5
    have s6 := lift (j := 5) (by decide) rfl h6
    have s7 := lift (j := 6) (by decide) rfl h7
    have s8 := lift (j := 7) (by decide) rfl h8
    simp only [run, s1, s2, s3, s4, s5, s6, s7, s8, Option.bind_some]
  · intro r hr
    have ne (j : Nat) (hj : j ∈ [1061, 1666, 1667, 1668, 1669, 1670, 1671, 1672]) : r ≠ j := by
      rintro rfl
      exact hr hj
    simp [t8, t7, t6, t5, t4, t3, t2, t1, next, setReg, ne 1061 (by decide), ne 1666 (by decide),
      ne 1667 (by decide), ne 1668 (by decide), ne 1669 (by decide), ne 1670 (by decide),
      ne 1671 (by decide), ne 1672 (by decide)]

theorem warpIndexLocalWith {A : List Assumption} [StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    (g : Nat) (t : TState) (hpc : t.pc = 26) (hf : t.fault = none) :
    ∃ u, run kernel A l g 8 t = some u ∧ u.pc = 34 ∧ u.fault = none ∧
      u.regs 1672 = some (b32 (warpIndex l g)) ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧
      ∀ r ∉ [1061, 1666, 1667, 1668, 1669, 1670, 1671, 1672], u.regs r = t.regs r := by
  obtain ⟨u, hRun, hPc, hFault, hWarp, _, hSub, hAcc, hFrame⟩ :=
    warpIndexLocalWithTid (A := A) hpre g t hpc hf
  exact ⟨u, hRun, hPc, hFault, hWarp, hSub, hAcc, hFrame⟩

/-- The two warp-index broadcasts have the same frame and broadcast from lane 0. -/
theorem warpBroadcastOut {l : Launch} {g : Nat} {t : TState} {stage : Fin 2}
    (hb : l.block = 512) (hp : t.pc = 34 + stage.val) (hf : t.fault = none)
    (hr : t.regs (if stage.val = 0 then 1672 else 1673) = some (b32 (warpIndex l g))) :
    out kernel [] l g t = .ev (broadcastTemplate t (if stage.val = 0 then 1673 else 1062)
      (b32 (warpIndex l g))) := by
  by_cases hz : stage.val = 0
  · rw [hz] at hp
    simp only [hz, ↓reduceIte] at hr ⊢
    exact idxOut hb hp hf hr Flow.code_34
  · have h₁ : stage.val = 1 := by have := stage.isLt; omega
    rw [h₁] at hp
    simp only [hz, ↓reduceIte] at hr ⊢
    exact idxOut hb hp hf hr Flow.code_35

/-- Firing a broadcast makes the received word available and advances exactly one pc. -/
theorem broadcastFires {t u : TState} {pc dst : Nat} {src : Value} {e : Event}
    (h : Fires pc (broadcastTemplate t dst src) e (some u)) :
    ∃ recv ok, e = ⟨pc, .shfl .idx src 0 31 recv ok⟩ ∧ u = next (setReg t dst recv) := by
  obtain ⟨recv, ok, he, hu⟩ := h
  exact ⟨recv, ok, he, Option.some.inj hu⟩

end
end PTX.Kernels.TmlFa4Fwd.Prologue
