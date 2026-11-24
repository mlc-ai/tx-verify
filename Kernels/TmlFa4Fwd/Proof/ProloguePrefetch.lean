-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Flow.Code.Part000
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Lemmas.Flow.Local

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section
set_option maxRecDepth 2000

private theorem tau_prefetch {l : Launch} {g pc i d : Nat} {t : TState} {address : Nat}
    (hp : t.pc = pc) (hf : t.fault = none)
    (hi : t.regs d = some (.ptr 64 true (.param (param i)) 0))
    (hm : l.paramObjects (param i) = some (mapParam i, address))
    (ha : address % 64 = 0) (hr : address + 128 ≤ 2 ^ 64)
    (hc : kernel.code[pc]? = some ⟨none, .prefetchTensorMap true 64 (.reg d)⟩) :
    tauStep kernel [] l g t = some (next t) := by
  have hok : (mapParam i).name = param i ∧ 0 < (mapParam i).bytes ∧ 0 < (mapParam i).alignment ∧
      address % (mapParam i).alignment = 0 ∧ address + (mapParam i).bytes ≤ 2 ^ 64 :=
    ⟨rfl, by norm_num [mapParam, ParamObjectDecl.bytes], by norm_num [mapParam,
        ParamObjectDecl.bytes],
      by simpa [mapParam] using ha, by simpa [mapParam, ParamObjectDecl.bytes] using hr⟩
  have he := PTX.Flow.exec_prefetchTensorMap (A := []) (g := g) hi (Or.inr rfl) hm hok
    (by simp)
  simp only [tauStep, out, hp, hf, hc, guardHolds, pure, Except.pure, ↓reduceIte, he,
    show (Op.prefetchTensorMap true 64 (.reg d)).isLocal = true by rfl]

private theorem tau_cvta {l : Launch} {g pc i r d : Nat} {t : TState}
    (hp : t.pc = pc) (hf : t.fault = none)
    (hi : t.regs r = some (.ptr 64 false (.param (param i)) 0))
    (hc : kernel.code[pc]? = some ⟨none, .addr (.cvta false .param 64 d (.reg r))⟩) :
    tauStep kernel [] l g t = some (next (setReg t d (.ptr 64 true (.param (param i)) 0))) := by
  have he : execLocal l g t (.addr (.cvta false .param 64 d (.reg r))) =
      .ok (next (setReg t d (.ptr 64 true (.param (param i)) 0))) := by
    rw [execLocal_cvta rfl, execCvta_param]
    simp [readValue, readReg, hi, bind, Except.bind, pure, Except.pure]
  have he' : execLocalA [] l g t (.addr (.cvta false .param 64 d (.reg r))) = _ := he
  simp only [tauStep, out, hp, hf, hc, guardHolds, pure, Except.pure, ↓reduceIte, he',
    show (Op.addr (.cvta false .param 64 d (.reg r))).isLocal = true by rfl]

theorem tau_testZero {l : Launch} {g pc d : Nat} {t : TState}
    (hp : t.pc = pc) (hf : t.fault = none) (hw : t.regs 1062 = some (b32 0))
    (hc : kernel.code[pc]? = some ⟨none,
      .int ⟨.setp .ne none, .int .b 32, false, [some d], [.reg 1062, .imm 0]⟩⟩) :
    tauStep kernel [] l g t = some (next (setReg t d (.pred false))) := by
  let i : IntInstr := ⟨.setp .ne none, .int .b 32, false, [some d], [.reg 1062, .imm 0]⟩
  have he : execLocal l g t (.int i) = .ok (next (setReg t d (.pred false))) := by
    rw [execLocal_int rfl]
    simp only [i, execInt, DType.width, readBits, readReg, hw, bind, Except.bind, pure, Except.pure]
    rfl
  have he' : execLocalA [] l g t (.int i) = _ := he
  have hc' : kernel.code[pc]? = some ⟨none, .int i⟩ := hc
  simp only [tauStep, out, hp, hf, hc', guardHolds, pure, Except.pure, ↓reduceIte, he',
    show (Op.int i).isLocal = true by rfl]

theorem tau_skip {l : Launch} {g pc d dst : Nat} {t : TState}
    (hp : t.pc = pc) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hr : t.regs d = some (.pred false))
    (hc : kernel.code[pc]? = some ⟨some (d, false), .bra dst false⟩) :
    tauStep kernel [] l g t = some (next t) := by
  simp [tauStep, out, hp, hf, hc, guardHolds, readReg, hr, bind, Except.bind, pure, Except.pure,
    skip, next, hs, ha]

/-- Warp 0 converts the three map pointers, runs their prefetch hints, and reaches the
first full-mask election. -/
theorem warp0PrefetchWith {A : List Assumption} [StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    (g : Nat) (t : TState) (hp : t.pc = 36) (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hw : t.regs 1062 = some (b32 0))
    (hq : t.regs 7291 = some (.ptr 64 false (.param (param 9)) 0))
    (ho : t.regs 7290 = some (.ptr 64 false (.param (param 10)) 0))
    (hb : t.regs 7289 = some (.ptr 64 false (.param (param 11)) 0)) :
    ∃ u, run kernel A l g 10 t = some u ∧ u.pc = 46 ∧ u.fault = none ∧ u.sub = 0 ∧ u.acc = [] ∧
      ∀ r ∉ [18, 7507, 7508, 7509, 19], u.regs r = t.regs r := by
  obtain ⟨hqm, hqa, hqr, -⟩ := hpre.maps 9 p.qMapAddress ⟨2, p.qMap⟩ (by simp)
  obtain ⟨hom, hoa, hor, -⟩ := hpre.maps 10 p.oMapAddress ⟨3, p.oMap⟩ (by simp)
  obtain ⟨hbm, hba, hbr, -⟩ := hpre.maps 11 p.biasMapAddress ⟨2, p.biasMap⟩ (by simp)
  let t1 := next (setReg t 18 (.pred false))
  let t2 := next t1
  let t3 := next (setReg t2 7507 (.ptr 64 true (.param (param 9)) 0))
  let t4 := next t3
  let t5 := next (setReg t4 7508 (.ptr 64 true (.param (param 10)) 0))
  let t6 := next t5
  let t7 := next (setReg t6 7509 (.ptr 64 true (.param (param 11)) 0))
  let t8 := next t7
  let t9 := next (setReg t8 19 (.pred false))
  let t10 := next t9
  have h1 : tauStep kernel [] l g t = some t1 := tau_testZero hp hf hw Flow.code_36
  have h2 : tauStep kernel [] l g t1 = some t2 :=
    tau_skip (t := t1) (by change t.pc + 1 = 37; rw [hp]) hf hs ha rfl Flow.code_37
  have h3 : tauStep kernel [] l g t2 = some t3 :=
    tau_cvta (t := t2) (pc := 38) (r := 7291) (by change t.pc + 2 = 38; rw [hp]) hf hq Flow.code_38
  have h4 : tauStep kernel [] l g t3 = some t4 :=
    tau_prefetch (t := t3) (pc := 39)
      (by change t.pc + 3 = 39; rw [hp]) hf rfl hqm hqa hqr Flow.code_39
  have h5 : tauStep kernel [] l g t4 = some t5 :=
    tau_cvta (t := t4) (pc := 40) (r := 7290) (by change t.pc + 4 = 40; rw [hp]) hf ho Flow.code_40
  have h6 : tauStep kernel [] l g t5 = some t6 :=
    tau_prefetch (t := t5) (pc := 41)
      (by change t.pc + 5 = 41; rw [hp]) hf rfl hom hoa hor Flow.code_41
  have h7 : tauStep kernel [] l g t6 = some t7 :=
    tau_cvta (t := t6) (pc := 42) (r := 7289) (by change t.pc + 6 = 42; rw [hp]) hf hb Flow.code_42
  have h8 : tauStep kernel [] l g t7 = some t8 :=
    tau_prefetch (t := t7) (pc := 43)
      (by change t.pc + 7 = 43; rw [hp]) hf rfl hbm hba hbr Flow.code_43
  have h9 : tauStep kernel [] l g t8 = some t9 :=
    tau_testZero (t := t8) (by change t.pc + 8 = 44; rw [hp]) hf hw Flow.code_44
  have h10 : tauStep kernel [] l g t9 = some t10 :=
    tau_skip (t := t9) (by change t.pc + 9 = 45; rw [hp]) hf hs ha rfl Flow.code_45
  refine ⟨t10, ?_, by change t.pc + 10 = 46; rw [hp], hf, hs, ha, ?_⟩
  · have transfer {s u : TState} {n : Nat} (hn : n < 179) (hpc : s.pc = n)
        (h : tauStep kernel [] l g s = some u) : tauStep kernel A l g s = some u :=
      startupTau (.inl (hpc ▸ hn)) h
    have pc₁ : t1.pc = 37 := by change t.pc + 1 = _; rw [hp]
    have pc₂ : t2.pc = 38 := by change t.pc + 2 = _; rw [hp]
    have pc₃ : t3.pc = 39 := by change t.pc + 3 = _; rw [hp]
    have pc₄ : t4.pc = 40 := by change t.pc + 4 = _; rw [hp]
    have pc₅ : t5.pc = 41 := by change t.pc + 5 = _; rw [hp]
    have pc₆ : t6.pc = 42 := by change t.pc + 6 = _; rw [hp]
    have pc₇ : t7.pc = 43 := by change t.pc + 7 = _; rw [hp]
    have pc₈ : t8.pc = 44 := by change t.pc + 8 = _; rw [hp]
    have pc₉ : t9.pc = 45 := by change t.pc + 9 = _; rw [hp]
    simp only [run, transfer (by decide) hp h1, transfer (by decide) pc₁ h2,
      transfer (by decide) pc₂ h3, transfer (by decide) pc₃ h4, transfer (by decide) pc₄ h5,
      transfer (by decide) pc₅ h6, transfer (by decide) pc₆ h7, transfer (by decide) pc₇ h8,
      transfer (by decide) pc₈ h9, transfer (by decide) pc₉ h10, Option.bind_some]
  · intro r hr
    have ne (d : Nat) (hd : d ∈ [18, 7507, 7508, 7509, 19]) : r ≠ d := by
      rintro rfl; exact hr hd
    simp [t10, t9, t8, t7, t6, t5, t4, t3, t2, t1, next, setReg, ne 18 (by decide),
      ne 7507 (by decide), ne 7508 (by decide), ne 7509 (by decide), ne 19 (by decide)]

end
end PTX.Kernels.TmlFa4Fwd.Prologue
