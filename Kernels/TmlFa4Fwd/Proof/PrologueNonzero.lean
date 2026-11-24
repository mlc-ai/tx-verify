-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Flow.Code.Part000
public import Kernels.TmlFa4Fwd.Flow.Code.Part001
public import Kernels.TmlFa4Fwd.Flow.Code.Part002
public import Lemmas.Flow.Next
public import Lemmas.Flow.Regs
public import Lemmas.Isa.Rule

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section
set_option maxRecDepth 2000

private def putReg (t : TState) (r : Nat) (v : Value) : TState := next (setReg t r v)

private theorem evalLocal {l : Launch} {g pc : Nat} {t u : TState} {op : Op}
    (hp : t.pc = pc) (hf : t.fault = none) (hc : kernel.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (he : execLocal l g t op = .ok u) :
    tauStep kernel [] l g t = some u := by
  have he' : execLocalA [] l g t op = .ok u := he
  simp only [tauStep, out, hp, hf, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, he']

private theorem evalTake {l : Launch} {g pc : Nat} {t : TState} {r dst : Nat}
    (hp : t.pc = pc) (hf : t.fault = none)
    (hc : kernel.code[pc]? = some ⟨some (r, false), .bra dst false⟩)
    (hr : t.regs r = some (.pred true)) :
    tauStep kernel [] l g t = some { t with pc := dst } := by
  simp [tauStep, out, hp, hf, hc, hr, guardHolds, readReg, Op.isLocal, execLocalA,
    execLocalRule, execLocal, Op.rule, execBranch, bind, Except.bind, pure, Except.pure]

private theorem evalNonzero {l : Launch} {g pc : Nat} {t : TState} {r w : Nat}
    (hp : t.pc = pc) (hf : t.fault = none) (hw : t.regs 1062 = some (b32 w))
    (hb : w < 2 ^ 32) (hn : w ≠ 0)
    (hc : kernel.code[pc]? = some ⟨none,
      .int ⟨.setp .ne none, .int .b 32, false, [some r], [.reg 1062, .imm 0]⟩⟩) :
    tauStep kernel [] l g t = some (putReg t r (.pred true)) := by
  apply evalLocal hp hf hc rfl
  rw [execLocal_int rfl]
  simp only [execInt, DType.width, readBits, readReg, hw, b32, bind, Except.bind,
    pure, Except.pure, truncBits_ofNat hb (by decide)]
  have he : compare .ne .b 32 (BitVec.ofNat 64 w) 0 = true := by
    have hw64 : w < 2 ^ 64 := lt_trans hb (by decide)
    have hword : (BitVec.ofNat 64 w).toNat = w := toNat_ofNat_lt hw64
    simp [compare, hword, hn]
  change Except.ok (putReg t r (.pred (compare .ne .b 32 (BitVec.ofNat 64 w) 0))) = _
  rw [he]

theorem evalSharedAdd {l : Launch} {g pc : Nat} {t : TState} {r off : Nat}
    (hp : t.pc = pc) (hf : t.fault = none) (hs : t.regs 2535 = some (b32 l.sharedBase))
    (hb : l.sharedBase + off < 2 ^ 32)
    (hc : kernel.code[pc]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some r], [.reg 2535, .imm off]⟩⟩) :
    tauStep kernel [] l g t = some (next (setReg t r (b32 (l.sharedBase + off)))) := by
  have hoff : off < 2 ^ 32 := by omega
  have hbase : l.sharedBase < 2 ^ 32 := by omega
  apply evalLocal hp hf hc rfl
  rw [execLocal_int rfl]
  simp only [execInt, DType.width, readValue, readBits, readReg, hs, b32, bind, Except.bind,
    pure, Except.pure, BitVec.ofInt_natCast, truncBits_ofNat hoff (by decide),
    truncBits_ofNat hbase (by decide)]
  change Except.ok (putReg t r (.bits 32 (truncBits 32
    (BitVec.ofNat 64 l.sharedBase + BitVec.ofNat 64 off)))) = _
  rw [← BitVec.ofNat_add, truncBits_ofNat hb (by decide)]
  rfl

private theorem nonzeroChunk0 {A : List Assumption} [StartupAgreement A]
    {l : Launch} {g w : Nat} {t : TState}
    (hw32 : w < 2 ^ 32) (hwn : w ≠ 0) (hb : ∀ off ≤ 336, l.sharedBase + off < 2 ^ 32)
    (hpc : t.pc = 36) (hf : t.fault = none)
    (hw : t.regs 1062 = some (b32 w)) (hs : t.regs 2535 = some (b32 l.sharedBase)) :
    ∃ u, run kernel A l g 8 t = some u ∧ u.pc = 69 ∧ u.fault = none ∧
      u.regs 1063 = some (b32 (l.sharedBase + 32)) ∧
      u.regs 1064 = some (b32 (l.sharedBase + 16)) ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧
      ∀ r ∉ [18, 19, 1063, 22, 1064], u.regs r = t.regs r := by
  let t1 := putReg t 18 (.pred true)
  have h1 : tauStep kernel [] l g t = some t1 :=
    evalNonzero (pc := 36) (t := t) hpc hf hw hw32 hwn Flow.code_36
  let t2 := { t1 with pc := 44 }
  have h2 : tauStep kernel [] l g t1 = some t2 :=
    evalTake (pc := 37) (t := t1) (by change t.pc + 1 = 37; rw [hpc]) hf Flow.code_37 rfl
  let t3 := putReg t2 19 (.pred true)
  have h3 : tauStep kernel [] l g t2 = some t3 :=
    evalNonzero (pc := 44) (t := t2) rfl hf hw hw32 hwn Flow.code_44
  let t4 := { t3 with pc := 52 }
  have h4 : tauStep kernel [] l g t3 = some t4 :=
    evalTake (pc := 45) (t := t3) rfl hf Flow.code_45 rfl
  let t5 := putReg t4 1063 (b32 (l.sharedBase + 32))
  have h5 : tauStep kernel [] l g t4 = some t5 :=
    evalSharedAdd (pc := 52) (t := t4) rfl hf hs (hb 32 (by decide)) Flow.code_52
  let t6 := putReg t5 22 (.pred true)
  have h6 : tauStep kernel [] l g t5 = some t6 :=
    evalNonzero (pc := 53) (t := t5) rfl hf hw hw32 hwn Flow.code_53
  let t7 := putReg t6 1064 (b32 (l.sharedBase + 16))
  have h7 : tauStep kernel [] l g t6 = some t7 :=
    evalSharedAdd (pc := 54) (t := t6) rfl hf hs (hb 16 (by decide)) Flow.code_54
  let t8 := { t7 with pc := 69 }
  have h8 : tauStep kernel [] l g t7 = some t8 :=
    evalTake (pc := 55) (t := t7) rfl hf Flow.code_55 rfl
  refine ⟨t8, ?_, rfl, hf, rfl, rfl, rfl, rfl, ?_⟩
  · have lift {s v : TState} (hc : StartupPc s.pc)
        (hs : tauStep kernel [] l g s = some v) : tauStep kernel A l g s = some v :=
      startupTau hc hs
    have s1 := lift (.inl (by rw [hpc]; decide)) h1
    have s2 := lift (.inl (by change t.pc + 1 < 179; rw [hpc]; decide)) h2
    have s3 := lift (show StartupPc 44 by decide) h3
    have s4 := lift (show StartupPc 45 by decide) h4
    have s5 := lift (show StartupPc 52 by decide) h5
    have s6 := lift (show StartupPc 53 by decide) h6
    have s7 := lift (show StartupPc 54 by decide) h7
    have s8 := lift (show StartupPc 55 by decide) h8
    simp only [run, s1, s2, s3, s4, s5, s6, s7, s8, Option.bind_some]
  · intro r hr
    have ne (d : Nat) (hd : d ∈ [18, 19, 1063, 22, 1064]) : r ≠ d := by
      rintro rfl
      exact hr hd
    simp [t8, t7, t6, t5, t4, t3, t2, t1, putReg, next, setReg, ne 18 (by decide), ne 19
      (by decide), ne 1063 (by decide), ne 22 (by decide), ne 1064 (by decide)]

private theorem nonzeroChunk1 {A : List Assumption} [StartupAgreement A]
    {l : Launch} {g w : Nat} {t : TState}
    (hw32 : w < 2 ^ 32) (hwn : w ≠ 0) (hb : ∀ off ≤ 336, l.sharedBase + off < 2 ^ 32)
    (hpc : t.pc = 69) (hf : t.fault = none)
    (hw : t.regs 1062 = some (b32 w)) (hs : t.regs 2535 = some (b32 l.sharedBase)) :
    ∃ u, run kernel A l g 8 t = some u ∧ u.pc = 102 ∧ u.fault = none ∧
      u.regs 1065 = some (b32 (l.sharedBase + 80)) ∧
      u.regs 1066 = some (b32 (l.sharedBase + 56)) ∧
      u.regs 1067 = some (b32 (l.sharedBase + 112)) ∧
      u.regs 1068 = some (b32 (l.sharedBase + 96)) ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧
      ∀ r ∉ [1065, 27, 1066, 1067, 32, 1068], u.regs r = t.regs r := by
  let t1 := putReg t 1065 (b32 (l.sharedBase + 80))
  have h1 : tauStep kernel [] l g t = some t1 :=
    evalSharedAdd (pc := 69) (t := t) hpc hf hs (hb 80 (by decide)) Flow.code_69
  let t2 := putReg t1 27 (.pred true)
  have h2 : tauStep kernel [] l g t1 = some t2 :=
    evalNonzero (pc := 70) (t := t1) (by change t.pc + 1 = 70; rw [hpc]) hf hw hw32 hwn Flow.code_70
  let t3 := putReg t2 1066 (b32 (l.sharedBase + 56))
  have h3 : tauStep kernel [] l g t2 = some t3 :=
    evalSharedAdd (pc := 71) (t := t2) (by change t.pc + 2 = 71; rw [hpc]) hf hs
      (hb 56 (by decide)) Flow.code_71
  let t4 := { t3 with pc := 86 }
  have h4 : tauStep kernel [] l g t3 = some t4 :=
    evalTake (pc := 72) (t := t3) (by change t.pc + 3 = 72; rw [hpc]) hf Flow.code_72 rfl
  let t5 := putReg t4 1067 (b32 (l.sharedBase + 112))
  have h5 : tauStep kernel [] l g t4 = some t5 :=
    evalSharedAdd (pc := 86) (t := t4) rfl hf hs (hb 112 (by decide)) Flow.code_86
  let t6 := putReg t5 32 (.pred true)
  have h6 : tauStep kernel [] l g t5 = some t6 :=
    evalNonzero (pc := 87) (t := t5) rfl hf hw hw32 hwn Flow.code_87
  let t7 := putReg t6 1068 (b32 (l.sharedBase + 96))
  have h7 : tauStep kernel [] l g t6 = some t7 :=
    evalSharedAdd (pc := 88) (t := t6) rfl hf hs (hb 96 (by decide)) Flow.code_88
  let t8 := { t7 with pc := 102 }
  have h8 : tauStep kernel [] l g t7 = some t8 :=
    evalTake (pc := 89) (t := t7) rfl hf Flow.code_89 rfl
  refine ⟨t8, ?_, rfl, hf, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · have lift {s v : TState} (hc : StartupPc s.pc)
        (hs : tauStep kernel [] l g s = some v) : tauStep kernel A l g s = some v :=
      startupTau hc hs
    have s1 := lift (.inl (by rw [hpc]; decide)) h1
    have s2 := lift (.inl (by change t.pc + 1 < 179; rw [hpc]; decide)) h2
    have s3 := lift (.inl (by change t.pc + 2 < 179; rw [hpc]; decide)) h3
    have s4 := lift (.inl (by change t.pc + 3 < 179; rw [hpc]; decide)) h4
    have s5 := lift (show StartupPc 86 by decide) h5
    have s6 := lift (show StartupPc 87 by decide) h6
    have s7 := lift (show StartupPc 88 by decide) h7
    have s8 := lift (show StartupPc 89 by decide) h8
    simp only [run, s1, s2, s3, s4, s5, s6, s7, s8, Option.bind_some]
  · intro r hr
    have ne (d : Nat) (hd : d ∈ [1065, 27, 1066, 1067, 32, 1068]) : r ≠ d := by
      rintro rfl
      exact hr hd
    simp [t8, t7, t6, t5, t4, t3, t2, t1, putReg, next, setReg, ne 1065 (by decide), ne 27
      (by decide), ne 1066 (by decide), ne 1067 (by decide), ne 32 (by decide), ne 1068
      (by decide)]

private theorem nonzeroChunk2 {A : List Assumption} [StartupAgreement A]
    {l : Launch} {g w : Nat} {t : TState}
    (hw32 : w < 2 ^ 32) (hwn : w ≠ 0) (hb : ∀ off ≤ 336, l.sharedBase + off < 2 ^ 32)
    (hpc : t.pc = 102) (hf : t.fault = none)
    (hw : t.regs 1062 = some (b32 w)) (hs : t.regs 2535 = some (b32 l.sharedBase)) :
    ∃ u, run kernel A l g 9 t = some u ∧ u.pc = 147 ∧ u.fault = none ∧
      u.regs 6495 = some (b32 (l.sharedBase + 144)) ∧
      u.regs 2390 = some (b32 (l.sharedBase + 208)) ∧
      u.regs 1069 = some (b32 (l.sharedBase + 192)) ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧
      ∀ r ∉ [6495, 37, 42, 2390, 47, 1069], u.regs r = t.regs r := by
  let t1 := putReg t 6495 (b32 (l.sharedBase + 144))
  have h1 : tauStep kernel [] l g t = some t1 :=
    evalSharedAdd (pc := 102) (t := t) hpc hf hs (hb 144 (by decide)) Flow.code_102
  let t2 := putReg t1 37 (.pred true)
  have h2 : tauStep kernel [] l g t1 = some t2 :=
    evalNonzero (pc := 103) (t := t1)
      (by change t.pc + 1 = 103; rw [hpc]) hf hw hw32 hwn Flow.code_103
  let t3 := { t2 with pc := 117 }
  have h3 : tauStep kernel [] l g t2 = some t3 :=
    evalTake (pc := 104) (t := t2) (by change t.pc + 2 = 104; rw [hpc]) hf Flow.code_104 rfl
  let t4 := putReg t3 42 (.pred true)
  have h4 : tauStep kernel [] l g t3 = some t4 :=
    evalNonzero (pc := 117) (t := t3) rfl hf hw hw32 hwn Flow.code_117
  let t5 := { t4 with pc := 131 }
  have h5 : tauStep kernel [] l g t4 = some t5 :=
    evalTake (pc := 118) (t := t4) rfl hf Flow.code_118 rfl
  let t6 := putReg t5 2390 (b32 (l.sharedBase + 208))
  have h6 : tauStep kernel [] l g t5 = some t6 :=
    evalSharedAdd (pc := 131) (t := t5) rfl hf hs (hb 208 (by decide)) Flow.code_131
  let t7 := putReg t6 47 (.pred true)
  have h7 : tauStep kernel [] l g t6 = some t7 :=
    evalNonzero (pc := 132) (t := t6) rfl hf hw hw32 hwn Flow.code_132
  let t8 := putReg t7 1069 (b32 (l.sharedBase + 192))
  have h8 : tauStep kernel [] l g t7 = some t8 :=
    evalSharedAdd (pc := 133) (t := t7) rfl hf hs (hb 192 (by decide)) Flow.code_133
  let t9 := { t8 with pc := 147 }
  have h9 : tauStep kernel [] l g t8 = some t9 :=
    evalTake (pc := 134) (t := t8) rfl hf Flow.code_134 rfl
  refine ⟨t9, ?_, rfl, hf, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · have lift {s v : TState} (hc : StartupPc s.pc)
        (hs : tauStep kernel [] l g s = some v) : tauStep kernel A l g s = some v :=
      startupTau hc hs
    have s1 := lift (.inl (by rw [hpc]; decide)) h1
    have s2 := lift (.inl (by change t.pc + 1 < 179; rw [hpc]; decide)) h2
    have s3 := lift (.inl (by change t.pc + 2 < 179; rw [hpc]; decide)) h3
    have s4 := lift (show StartupPc 117 by decide) h4
    have s5 := lift (show StartupPc 118 by decide) h5
    have s6 := lift (show StartupPc 131 by decide) h6
    have s7 := lift (show StartupPc 132 by decide) h7
    have s8 := lift (show StartupPc 133 by decide) h8
    have s9 := lift (show StartupPc 134 by decide) h9
    simp only [run, s1, s2, s3, s4, s5, s6, s7, s8, s9, Option.bind_some]
  · intro r hr
    have ne (d : Nat) (hd : d ∈ [6495, 37, 42, 2390, 47, 1069]) : r ≠ d := by
      rintro rfl
      exact hr hd
    simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, putReg, next, setReg, ne 6495 (by decide), ne 37
      (by decide), ne 42 (by decide), ne 2390 (by decide), ne 47 (by decide), ne 1069 (by decide)]

private theorem nonzeroChunk3 {A : List Assumption} [StartupAgreement A]
    {l : Launch} {g w : Nat} {t : TState}
    (hw32 : w < 2 ^ 32) (hwn : w ≠ 0) (hb : ∀ off ≤ 336, l.sharedBase + off < 2 ^ 32)
    (hpc : t.pc = 147) (hf : t.fault = none)
    (hw : t.regs 1062 = some (b32 w)) (hs : t.regs 2535 = some (b32 l.sharedBase)) :
    ∃ u, run kernel A l g 7 t = some u ∧ u.pc = 172 ∧ u.fault = none ∧
      u.regs 1070 = some (b32 (l.sharedBase + 320)) ∧
      u.regs 6497 = some (b32 (l.sharedBase + 224)) ∧
      u.regs 1071 = some (b32 (l.sharedBase + 336)) ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧
      ∀ r ∉ [1070, 52, 6497, 57, 1071], u.regs r = t.regs r := by
  let t1 := putReg t 1070 (b32 (l.sharedBase + 320))
  have h1 : tauStep kernel [] l g t = some t1 :=
    evalSharedAdd (pc := 147) (t := t) hpc hf hs (hb 320 (by decide)) Flow.code_147
  let t2 := putReg t1 52 (.pred true)
  have h2 : tauStep kernel [] l g t1 = some t2 :=
    evalNonzero (pc := 148) (t := t1)
      (by change t.pc + 1 = 148; rw [hpc]) hf hw hw32 hwn Flow.code_148
  let t3 := putReg t2 6497 (b32 (l.sharedBase + 224))
  have h3 : tauStep kernel [] l g t2 = some t3 :=
    evalSharedAdd (pc := 149) (t := t2) (by change t.pc + 2 = 149; rw [hpc]) hf hs
      (hb 224 (by decide)) Flow.code_149
  let t4 := { t3 with pc := 163 }
  have h4 : tauStep kernel [] l g t3 = some t4 :=
    evalTake (pc := 150) (t := t3) (by change t.pc + 3 = 150; rw [hpc]) hf Flow.code_150 rfl
  let t5 := putReg t4 57 (.pred true)
  have h5 : tauStep kernel [] l g t4 = some t5 :=
    evalNonzero (pc := 163) (t := t4) rfl hf hw hw32 hwn Flow.code_163
  let t6 := putReg t5 1071 (b32 (l.sharedBase + 336))
  have h6 : tauStep kernel [] l g t5 = some t6 :=
    evalSharedAdd (pc := 164) (t := t5) rfl hf hs (hb 336 (by decide)) Flow.code_164
  let t7 := { t6 with pc := 172 }
  have h7 : tauStep kernel [] l g t6 = some t7 :=
    evalTake (pc := 165) (t := t6) rfl hf Flow.code_165 rfl
  refine ⟨t7, ?_, rfl, hf, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · have lift {s v : TState} (hc : StartupPc s.pc)
        (hs : tauStep kernel [] l g s = some v) : tauStep kernel A l g s = some v :=
      startupTau hc hs
    have s1 := lift (.inl (by rw [hpc]; decide)) h1
    have s2 := lift (.inl (by change t.pc + 1 < 179; rw [hpc]; decide)) h2
    have s3 := lift (.inl (by change t.pc + 2 < 179; rw [hpc]; decide)) h3
    have s4 := lift (.inl (by change t.pc + 3 < 179; rw [hpc]; decide)) h4
    have s5 := lift (show StartupPc 163 by decide) h5
    have s6 := lift (show StartupPc 164 by decide) h6
    have s7 := lift (show StartupPc 165 by decide) h7
    simp only [run, s1, s2, s3, s4, s5, s6, s7, Option.bind_some]
  · intro r hr
    have ne (d : Nat) (hd : d ∈ [1070, 52, 6497, 57, 1071]) : r ≠ d := by
      rintro rfl
      exact hr hd
    simp [t7, t6, t5, t4, t3, t2, t1, putReg, next, setReg, ne 1070 (by decide), ne 52 (by decide),
      ne 6497 (by decide), ne 57 (by decide), ne 1071 (by decide)]

/-- The nonzero warps skip the warp-0-only prefetch and barrier initialization and converge at
`fence.mbarrier_init`. The barrier addresses computed on that path are available to each role. -/
theorem nonzeroWarpWith {A : List Assumption} [StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    (g w : Nat) (t : TState) (hwpos : 0 < w) (hwlim : w < 16)
    (hpc : t.pc = 36) (hf : t.fault = none)
    (hw : t.regs 1062 = some (b32 w)) (hs : t.regs 2535 = some (b32 l.sharedBase)) :
    ∃ u, run kernel A l g 32 t = some u ∧ u.pc = 172 ∧ u.fault = none ∧
      u.regs 1063 = some (b32 (l.sharedBase + 32)) ∧
      u.regs 1064 = some (b32 (l.sharedBase + 16)) ∧
      u.regs 1065 = some (b32 (l.sharedBase + 80)) ∧
      u.regs 1066 = some (b32 (l.sharedBase + 56)) ∧
      u.regs 1067 = some (b32 (l.sharedBase + 112)) ∧
      u.regs 1068 = some (b32 (l.sharedBase + 96)) ∧
      u.regs 6495 = some (b32 (l.sharedBase + 144)) ∧
      u.regs 2390 = some (b32 (l.sharedBase + 208)) ∧
      u.regs 1069 = some (b32 (l.sharedBase + 192)) ∧
      u.regs 1070 = some (b32 (l.sharedBase + 320)) ∧
      u.regs 6497 = some (b32 (l.sharedBase + 224)) ∧
      u.regs 1071 = some (b32 (l.sharedBase + 336)) ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧
      ∀ r ∉ [18, 19, 1063, 22, 1064, 1065, 27, 1066, 1067, 32, 1068, 6495,
        37, 42, 2390, 47, 1069, 1070, 52, 6497, 57, 1071], u.regs r = t.regs r := by
  have hw32 : w < 2 ^ 32 := by omega
  have hwn : w ≠ 0 := by omega
  have hb (off : Nat) (ho : off ≤ 336) : l.sharedBase + off < 2 ^ 32 := by
    have := hpre.shared.2.1
    omega
  obtain ⟨u0, hr0, hp0, hf0, hs1063, hs1064, hSub0, hAcc0, hx0⟩ :=
    nonzeroChunk0 (A := A) (g := g) hw32 hwn hb hpc hf hw hs
  have hw0 : u0.regs 1062 = some (b32 w) := (hx0 1062 (by decide)).trans hw
  have hsbase0 : u0.regs 2535 = some (b32 l.sharedBase) := (hx0 2535 (by decide)).trans hs
  obtain ⟨u1, hr1, hp1, hf1, hs1065, hs1066, hs1067, hs1068, hSub1, hAcc1, hx1⟩ :=
    nonzeroChunk1 (A := A) (g := g) hw32 hwn hb hp0 hf0 hw0 hsbase0
  have hw1 : u1.regs 1062 = some (b32 w) := (hx1 1062 (by decide)).trans hw0
  have hsbase1 : u1.regs 2535 = some (b32 l.sharedBase) := (hx1 2535 (by decide)).trans hsbase0
  obtain ⟨u2, hr2, hp2, hf2, hs6495, hs2390, hs1069, hSub2, hAcc2, hx2⟩ :=
    nonzeroChunk2 (A := A) (g := g) hw32 hwn hb hp1 hf1 hw1 hsbase1
  have hw2 : u2.regs 1062 = some (b32 w) := (hx2 1062 (by decide)).trans hw1
  have hsbase2 : u2.regs 2535 = some (b32 l.sharedBase) := (hx2 2535 (by decide)).trans hsbase1
  obtain ⟨u3, hr3, hp3, hf3, hs1070, hs6497, hs1071, hSub3, hAcc3, hx3⟩ :=
    nonzeroChunk3 (A := A) (g := g) hw32 hwn hb hp2 hf2 hw2 hsbase2
  refine ⟨u3, run_comp (run_comp (run_comp hr0 hr1) hr2) hr3, hp3, hf3,
    (hx3 1063 (by decide)).trans
      ((hx2 1063 (by decide)).trans ((hx1 1063 (by decide)).trans (hs1063))),
    (hx3 1064 (by decide)).trans
      ((hx2 1064 (by decide)).trans ((hx1 1064 (by decide)).trans (hs1064))),
    (hx3 1065 (by decide)).trans ((hx2 1065 (by decide)).trans (hs1065)),
    (hx3 1066 (by decide)).trans ((hx2 1066 (by decide)).trans (hs1066)),
    (hx3 1067 (by decide)).trans ((hx2 1067 (by decide)).trans (hs1067)),
    (hx3 1068 (by decide)).trans ((hx2 1068 (by decide)).trans (hs1068)),
    (hx3 6495 (by decide)).trans (hs6495),
    (hx3 2390 (by decide)).trans (hs2390),
    (hx3 1069 (by decide)).trans (hs1069),
    hs1070,
    hs6497,
    hs1071,
    hSub3.trans (hSub2.trans (hSub1.trans hSub0)),
    hAcc3.trans (hAcc2.trans (hAcc1.trans hAcc0)),
    ?_⟩
  intro r hr
  change r ∉ [18, 19, 1063, 22, 1064] ++ [1065, 27, 1066, 1067, 32, 1068] ++
    [6495, 37, 42, 2390, 47, 1069] ++ [1070, 52, 6497, 57, 1071] at hr
  simp only [List.mem_append, not_or] at hr
  exact (hx3 r hr.2).trans ((hx2 r hr.1.2).trans ((hx1 r hr.1.1.2).trans (hx0 r hr.1.1.1)))

end
end PTX.Kernels.TmlFa4Fwd.Prologue
