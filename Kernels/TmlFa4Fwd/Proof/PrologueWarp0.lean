-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueElect
public import Kernels.TmlFa4Fwd.Proof.PrologueInit
public import Kernels.TmlFa4Fwd.Proof.PrologueNonzero
public import Kernels.TmlFa4Fwd.Proof.ProloguePrefetch

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section

/-- A local interval between the initializer group join and the next election. -/
structure Warp0Join where
  entry : Nat
  exit : Nat
  writes : List Nat
  addresses : List (Nat × Nat)

def warp0Joins : Vector Warp0Join 8 := #v[
  ⟨52, 56, [1063, 22, 1064], [(1063, 32), (1064, 16)]⟩,
  ⟨69, 73, [1065, 27, 1066], [(1065, 80), (1066, 56)]⟩,
  ⟨86, 90, [1067, 32, 1068], [(1067, 112), (1068, 96)]⟩,
  ⟨102, 105, [6495, 37], [(6495, 144)]⟩,
  ⟨117, 119, [42], []⟩,
  ⟨131, 135, [2390, 47, 1069], [(2390, 208), (1069, 192)]⟩,
  ⟨147, 151, [1070, 52, 6497], [(1070, 320), (6497, 224)]⟩,
  ⟨163, 166, [57, 1071], [(1071, 336)]⟩]

def warp0Join (i : Fin 8) : Warp0Join := warp0Joins[i]

/-- The local joins compute every derived address used by the elected initializer, then enter
its full-mask election. -/
theorem warp0JoinRunWith {A : List Assumption} [StartupAgreement A]
    {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m)
    (i : Fin 8) (g : Nat) (t : TState) (hp : t.pc = (warp0Join i).entry)
    (hf : t.fault = none) (hs : t.sub = 0) (ha : t.acc = [])
    (hw : t.regs 1062 = some (b32 0)) (hbase : t.regs 2535 = some (b32 l.sharedBase)) :
    ∃ u, run kernel A l g ((warp0Join i).exit - (warp0Join i).entry) t = some u ∧
      At u (warp0Join i).exit ((warp0Join i).addresses.map fun (r, off) =>
        (r, b32 (l.sharedBase + off))) ∧
      ∀ r ∉ (warp0Join i).writes, u.regs r = t.regs r := by
  have hr (off : Nat) (ho : off ≤ 336) : l.sharedBase + off < 2 ^ 32 := by
    have := hpre.shared.2.1
    omega
  have lift {s u : TState} (hPc : s.pc < 179) (h : tauStep kernel [] l g s = some u) :
      tauStep kernel A l g s = some u := startupTau (.inl hPc) h
  fin_cases i
  · change t.pc = 52 at hp
    let t1 := next (setReg t 1063 (b32 (l.sharedBase + 32)))
    have h1 : tauStep kernel [] l g t = some t1 :=
      evalSharedAdd (pc := 52) (t := t) hp hf hbase (hr 32 (by decide))
        Flow.code_52
    let t2 := next (setReg t1 22 (.pred false))
    have h2 : tauStep kernel [] l g t1 = some t2 :=
      tau_testZero (pc := 53) (t := t1) (by change t.pc + 1 = 53; rw [hp]) hf hw Flow.code_53
    let t3 := next (setReg t2 1064 (b32 (l.sharedBase + 16)))
    have h3 : tauStep kernel [] l g t2 = some t3 :=
      evalSharedAdd (pc := 54) (t := t2) (by change t.pc + 2 = 54; rw [hp]) hf hbase
        (hr 16 (by decide))
        Flow.code_54
    let t4 := next t3
    have h4 : tauStep kernel [] l g t3 = some t4 :=
      tau_skip (pc := 55) (t := t3) (by change t.pc + 3 = 55; rw [hp]) hf hs ha rfl Flow.code_55
    change ∃ u, run kernel A l g 4 t = some u ∧ At u 56
      [(1063, b32 (l.sharedBase + 32)), (1064, b32 (l.sharedBase + 16))] ∧ ∀ r ∉ [1063, 22,
        1064], u.regs r = t.regs r
    refine ⟨t4, ?_, ⟨by change t.pc + 4 = 56; rw [hp], hs, ha, hf, ?_⟩, ?_⟩
    · simp only [run,
        lift (show t.pc < 179 by omega) h1,
        lift (show t.pc + 1 < 179 by omega) h2,
        lift (show t.pc + 2 < 179 by omega) h3,
        lift (show t.pc + 3 < 179 by omega) h4, Option.bind_some]
    · repeat' constructor
    · intro r hnot
      have ne (d : Nat) (hd : d ∈ [1063, 22, 1064]) : r ≠ d := by
        rintro rfl
        exact hnot hd
      simp [t1, t2, t3, t4, next, setReg, ne 1063 (by decide), ne 22 (by decide), ne 1064
        (by decide)]
  · change t.pc = 69 at hp
    let t1 := next (setReg t 1065 (b32 (l.sharedBase + 80)))
    have h1 : tauStep kernel [] l g t = some t1 :=
      evalSharedAdd (pc := 69) (t := t) hp hf hbase (hr 80 (by decide))
        Flow.code_69
    let t2 := next (setReg t1 27 (.pred false))
    have h2 : tauStep kernel [] l g t1 = some t2 :=
      tau_testZero (pc := 70) (t := t1) (by change t.pc + 1 = 70; rw [hp]) hf hw Flow.code_70
    let t3 := next (setReg t2 1066 (b32 (l.sharedBase + 56)))
    have h3 : tauStep kernel [] l g t2 = some t3 :=
      evalSharedAdd (pc := 71) (t := t2) (by change t.pc + 2 = 71; rw [hp]) hf hbase
        (hr 56 (by decide))
        Flow.code_71
    let t4 := next t3
    have h4 : tauStep kernel [] l g t3 = some t4 :=
      tau_skip (pc := 72) (t := t3) (by change t.pc + 3 = 72; rw [hp]) hf hs ha rfl Flow.code_72
    change ∃ u, run kernel A l g 4 t = some u ∧ At u 73
      [(1065, b32 (l.sharedBase + 80)), (1066, b32 (l.sharedBase + 56))] ∧ ∀ r ∉ [1065, 27,
        1066], u.regs r = t.regs r
    refine ⟨t4, ?_, ⟨by change t.pc + 4 = 73; rw [hp], hs, ha, hf, ?_⟩, ?_⟩
    · simp only [run,
        lift (show t.pc < 179 by omega) h1,
        lift (show t.pc + 1 < 179 by omega) h2,
        lift (show t.pc + 2 < 179 by omega) h3,
        lift (show t.pc + 3 < 179 by omega) h4, Option.bind_some]
    · repeat' constructor
    · intro r hnot
      have ne (d : Nat) (hd : d ∈ [1065, 27, 1066]) : r ≠ d := by
        rintro rfl
        exact hnot hd
      simp [t1, t2, t3, t4, next, setReg, ne 1065 (by decide), ne 27 (by decide), ne 1066
        (by decide)]
  · change t.pc = 86 at hp
    let t1 := next (setReg t 1067 (b32 (l.sharedBase + 112)))
    have h1 : tauStep kernel [] l g t = some t1 :=
      evalSharedAdd (pc := 86) (t := t) hp hf hbase (hr 112 (by decide))
        Flow.code_86
    let t2 := next (setReg t1 32 (.pred false))
    have h2 : tauStep kernel [] l g t1 = some t2 :=
      tau_testZero (pc := 87) (t := t1) (by change t.pc + 1 = 87; rw [hp]) hf hw Flow.code_87
    let t3 := next (setReg t2 1068 (b32 (l.sharedBase + 96)))
    have h3 : tauStep kernel [] l g t2 = some t3 :=
      evalSharedAdd (pc := 88) (t := t2) (by change t.pc + 2 = 88; rw [hp]) hf hbase
        (hr 96 (by decide))
        Flow.code_88
    let t4 := next t3
    have h4 : tauStep kernel [] l g t3 = some t4 :=
      tau_skip (pc := 89) (t := t3) (by change t.pc + 3 = 89; rw [hp]) hf hs ha rfl Flow.code_89
    change ∃ u, run kernel A l g 4 t = some u ∧ At u 90
      [(1067, b32 (l.sharedBase + 112)), (1068, b32 (l.sharedBase + 96))] ∧ ∀ r ∉ [1067, 32,
        1068], u.regs r = t.regs r
    refine ⟨t4, ?_, ⟨by change t.pc + 4 = 90; rw [hp], hs, ha, hf, ?_⟩, ?_⟩
    · simp only [run,
        lift (show t.pc < 179 by omega) h1,
        lift (show t.pc + 1 < 179 by omega) h2,
        lift (show t.pc + 2 < 179 by omega) h3,
        lift (show t.pc + 3 < 179 by omega) h4, Option.bind_some]
    · repeat' constructor
    · intro r hnot
      have ne (d : Nat) (hd : d ∈ [1067, 32, 1068]) : r ≠ d := by
        rintro rfl
        exact hnot hd
      simp [t1, t2, t3, t4, next, setReg, ne 1067 (by decide), ne 32 (by decide), ne 1068
        (by decide)]
  · change t.pc = 102 at hp
    let t1 := next (setReg t 6495 (b32 (l.sharedBase + 144)))
    have h1 : tauStep kernel [] l g t = some t1 :=
      evalSharedAdd (pc := 102) (t := t) hp hf hbase (hr 144 (by decide))
        Flow.code_102
    let t2 := next (setReg t1 37 (.pred false))
    have h2 : tauStep kernel [] l g t1 = some t2 :=
      tau_testZero (pc := 103) (t := t1) (by change t.pc + 1 = 103; rw [hp]) hf hw Flow.code_103
    let t3 := next t2
    have h3 : tauStep kernel [] l g t2 = some t3 :=
      tau_skip (pc := 104) (t := t2) (by change t.pc + 2 = 104; rw [hp]) hf hs ha rfl Flow.code_104
    change ∃ u, run kernel A l g 3 t = some u ∧ At u 105
      [(6495, b32 (l.sharedBase + 144))] ∧ ∀ r ∉ [6495, 37], u.regs r = t.regs r
    refine ⟨t3, ?_, ⟨by change t.pc + 3 = 105; rw [hp], hs, ha, hf, ?_⟩, ?_⟩
    · simp only [run,
        lift (show t.pc < 179 by omega) h1,
        lift (show t.pc + 1 < 179 by omega) h2,
        lift (show t.pc + 2 < 179 by omega) h3, Option.bind_some]
    · repeat' constructor
    · intro r hnot
      have ne (d : Nat) (hd : d ∈ [6495, 37]) : r ≠ d := by
        rintro rfl
        exact hnot hd
      simp [t1, t2, t3, next, setReg, ne 6495 (by decide), ne 37 (by decide)]
  · change t.pc = 117 at hp
    let t1 := next (setReg t 42 (.pred false))
    have h1 : tauStep kernel [] l g t = some t1 :=
      tau_testZero (pc := 117) (t := t) hp hf hw Flow.code_117
    let t2 := next t1
    have h2 : tauStep kernel [] l g t1 = some t2 :=
      tau_skip (pc := 118) (t := t1) (by change t.pc + 1 = 118; rw [hp]) hf hs ha rfl Flow.code_118
    change ∃ u, run kernel A l g 2 t = some u ∧ At u 119
      [] ∧ ∀ r ∉ [42], u.regs r = t.regs r
    refine ⟨t2, ?_, ⟨by change t.pc + 2 = 119; rw [hp], hs, ha, hf, ?_⟩, ?_⟩
    · simp only [run,
        lift (show t.pc < 179 by omega) h1,
        lift (show t.pc + 1 < 179 by omega) h2, Option.bind_some]
    · repeat' constructor
    · intro r hnot
      have ne (d : Nat) (hd : d ∈ [42]) : r ≠ d := by
        rintro rfl
        exact hnot hd
      simp [t1, t2, next, setReg, ne 42 (by decide)]
  · change t.pc = 131 at hp
    let t1 := next (setReg t 2390 (b32 (l.sharedBase + 208)))
    have h1 : tauStep kernel [] l g t = some t1 :=
      evalSharedAdd (pc := 131) (t := t) hp hf hbase (hr 208 (by decide))
        Flow.code_131
    let t2 := next (setReg t1 47 (.pred false))
    have h2 : tauStep kernel [] l g t1 = some t2 :=
      tau_testZero (pc := 132) (t := t1) (by change t.pc + 1 = 132; rw [hp]) hf hw Flow.code_132
    let t3 := next (setReg t2 1069 (b32 (l.sharedBase + 192)))
    have h3 : tauStep kernel [] l g t2 = some t3 :=
      evalSharedAdd (pc := 133) (t := t2) (by change t.pc + 2 = 133; rw [hp]) hf hbase
        (hr 192 (by decide))
        Flow.code_133
    let t4 := next t3
    have h4 : tauStep kernel [] l g t3 = some t4 :=
      tau_skip (pc := 134) (t := t3) (by change t.pc + 3 = 134; rw [hp]) hf hs ha rfl Flow.code_134
    change ∃ u, run kernel A l g 4 t = some u ∧ At u 135
      [(2390, b32 (l.sharedBase + 208)), (1069, b32 (l.sharedBase + 192))] ∧ ∀ r ∉ [2390, 47,
        1069], u.regs r = t.regs r
    refine ⟨t4, ?_, ⟨by change t.pc + 4 = 135; rw [hp], hs, ha, hf, ?_⟩, ?_⟩
    · simp only [run,
        lift (show t.pc < 179 by omega) h1,
        lift (show t.pc + 1 < 179 by omega) h2,
        lift (show t.pc + 2 < 179 by omega) h3,
        lift (show t.pc + 3 < 179 by omega) h4, Option.bind_some]
    · repeat' constructor
    · intro r hnot
      have ne (d : Nat) (hd : d ∈ [2390, 47, 1069]) : r ≠ d := by
        rintro rfl
        exact hnot hd
      simp [t1, t2, t3, t4, next, setReg, ne 2390 (by decide), ne 47 (by decide), ne 1069
        (by decide)]
  · change t.pc = 147 at hp
    let t1 := next (setReg t 1070 (b32 (l.sharedBase + 320)))
    have h1 : tauStep kernel [] l g t = some t1 :=
      evalSharedAdd (pc := 147) (t := t) hp hf hbase (hr 320 (by decide))
        Flow.code_147
    let t2 := next (setReg t1 52 (.pred false))
    have h2 : tauStep kernel [] l g t1 = some t2 :=
      tau_testZero (pc := 148) (t := t1) (by change t.pc + 1 = 148; rw [hp]) hf hw Flow.code_148
    let t3 := next (setReg t2 6497 (b32 (l.sharedBase + 224)))
    have h3 : tauStep kernel [] l g t2 = some t3 :=
      evalSharedAdd (pc := 149) (t := t2) (by change t.pc + 2 = 149; rw [hp]) hf hbase
        (hr 224 (by decide))
        Flow.code_149
    let t4 := next t3
    have h4 : tauStep kernel [] l g t3 = some t4 :=
      tau_skip (pc := 150) (t := t3) (by change t.pc + 3 = 150; rw [hp]) hf hs ha rfl Flow.code_150
    change ∃ u, run kernel A l g 4 t = some u ∧ At u 151
      [(1070, b32 (l.sharedBase + 320)), (6497, b32 (l.sharedBase + 224))] ∧ ∀ r ∉ [1070, 52,
        6497], u.regs r = t.regs r
    refine ⟨t4, ?_, ⟨by change t.pc + 4 = 151; rw [hp], hs, ha, hf, ?_⟩, ?_⟩
    · simp only [run,
        lift (show t.pc < 179 by omega) h1,
        lift (show t.pc + 1 < 179 by omega) h2,
        lift (show t.pc + 2 < 179 by omega) h3,
        lift (show t.pc + 3 < 179 by omega) h4, Option.bind_some]
    · repeat' constructor
    · intro r hnot
      have ne (d : Nat) (hd : d ∈ [1070, 52, 6497]) : r ≠ d := by
        rintro rfl
        exact hnot hd
      simp [t1, t2, t3, t4, next, setReg, ne 1070 (by decide), ne 52 (by decide), ne 6497
        (by decide)]
  · change t.pc = 163 at hp
    let t1 := next (setReg t 57 (.pred false))
    have h1 : tauStep kernel [] l g t = some t1 :=
      tau_testZero (pc := 163) (t := t) hp hf hw Flow.code_163
    let t2 := next (setReg t1 1071 (b32 (l.sharedBase + 336)))
    have h2 : tauStep kernel [] l g t1 = some t2 :=
      evalSharedAdd (pc := 164) (t := t1) (by change t.pc + 1 = 164; rw [hp]) hf hbase
        (hr 336 (by decide))
        Flow.code_164
    let t3 := next t2
    have h3 : tauStep kernel [] l g t2 = some t3 :=
      tau_skip (pc := 165) (t := t2) (by change t.pc + 2 = 165; rw [hp]) hf hs ha rfl Flow.code_165
    change ∃ u, run kernel A l g 3 t = some u ∧ At u 166
      [(1071, b32 (l.sharedBase + 336))] ∧ ∀ r ∉ [57, 1071], u.regs r = t.regs r
    refine ⟨t3, ?_, ⟨by change t.pc + 3 = 166; rw [hp], hs, ha, hf, ?_⟩, ?_⟩
    · simp only [run,
        lift (show t.pc < 179 by omega) h1,
        lift (show t.pc + 1 < 179 by omega) h2,
        lift (show t.pc + 2 < 179 by omega) h3, Option.bind_some]
    · repeat' constructor
    · intro r hnot
      have ne (d : Nat) (hd : d ∈ [57, 1071]) : r ≠ d := by
        rintro rfl
        exact hnot hd
      simp [t1, t2, t3, next, setReg, ne 57 (by decide), ne 1071 (by decide)]

end
end PTX.Kernels.TmlFa4Fwd.Prologue
