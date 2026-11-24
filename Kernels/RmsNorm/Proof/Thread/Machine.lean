-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Start
public import Kernels.RmsNorm.Proof.Thread.StepShfl0
public import Kernels.RmsNorm.Proof.Thread.StepSt
public import Kernels.RmsNorm.Proof.Thread.StepLd1
public import Kernels.RmsNorm.Proof.Thread.StepOut
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # The thread's machine is sound

The obligations of the site machine (`Flow.Code.Sound`): the start reaches the warp-index
shuffle, and every site is an unguarded event instruction whose step reaches its successor or a
dead state. No site has an undefined-behaviour template (`tmplOk`): a thread performs undefined
behaviour only after the machine has stopped. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A four-element load of 32-bit words from global memory through a 64-bit register. -/
abbrev ldGlobal4 (base d0 d1 d2 d3 : Nat) : Op :=
  .mem { kind := .load, space := some .global, sem := .weak, elem := .int .b 32, vec := 4,
         addr := ⟨.reg base 64, 0⟩, dsts := [some d0, some d1, some d2, some d3] }

/-- A four-element load of `f32` from the thread's shared window through a 32-bit register. -/
abbrev ldShared4 (base d0 d1 d2 d3 : Nat) : Op :=
  .mem { kind := .load, space := some (.shared .cta), sem := .weak, elem := .float .f32, vec := 4,
         addr := ⟨.reg base 32, 0⟩, dsts := [some d0, some d1, some d2, some d3] }

/-- A four-element store of 32-bit words to global memory through a 64-bit register. -/
abbrev stGlobal4 (base : Nat) (srcs : List Opnd) : Op :=
  .mem { kind := .store, space := some .global, sem := .weak, elem := .int .b 32, vec := 4,
         addr := ⟨.reg base 64, 0⟩, srcs }

/-- A four-element store of `f32` to the thread's shared window through a 32-bit register. -/
abbrev stShared4 (base : Nat) (srcs : List Opnd) : Op :=
  .mem { kind := .store, space := some (.shared .cta), sem := .weak, elem := .float .f32, vec := 4,
         addr := ⟨.reg base 32, 0⟩, srcs }

/-- A scalar load of `f32` from the thread's shared window. -/
abbrev ldShared1 (dst base : Nat) : Op :=
  .mem { kind := .load, space := some (.shared .cta), sem := .weak, elem := .float .f32,
         addr := ⟨.reg base 32, 0⟩, dsts := [some dst] }

/-- A scalar store of `f32` to the thread's shared window. -/
abbrev stShared1 (base src : Nat) : Op :=
  .mem { kind := .store, space := some (.shared .cta), sem := .weak, elem := .float .f32,
         addr := ⟨.reg base 32, 0⟩, srcs := [.reg src] }

/-- A butterfly shuffle of one register with full lane operands `b` and `c` and mask `m`. -/
abbrev shflBfly (dst a b c m : Nat) : Op :=
  .warp { kind := .shfl .bfly, ty := some (.int .b 32), dsts := [some dst],
          srcs := [.reg a, .reg b, .reg c], mask := some (.reg m) }

/-- The warp-index shuffle `shfl.sync.idx.b32` of the first site. -/
abbrev shflIdx0 : Op :=
  .warp { kind := .shfl .idx, ty := some (.int .b 32), dsts := [some 46, some 1],
          srcs := [.reg 43, .imm 0, .imm 31], mask := some (.imm (-1)) }

/-- The instruction at each site. -/
def siteOp (d : D) : Op :=
  match d.site with
  | .shfl0 => shflIdx0
  | .ldxa => ldGlobal4 287 53 54 55 56
  | .stxa0 => stShared4 161 [.reg 65, .reg 66, .reg 67, .reg 68]
  | .stxa1 => stShared4 166 [.reg 69, .reg 70, .reg 71, .reg 72]
  | .ldxb => ldGlobal4 288 73 74 75 76
  | .stxb0 => stShared4 219 [.reg 85, .reg 86, .reg 87, .reg 88]
  | .stxb1 => stShared4 224 [.reg 89, .reg 90, .reg 91, .reg 92]
  | .bfa 0 => shflBfly 93 94 95 96 97
  | .bfa 1 => shflBfly 98 99 100 96 97
  | .bfa 2 => shflBfly 101 102 103 96 97
  | .bfa 3 => shflBfly 104 105 106 96 97
  | .bfa _ => shflBfly 107 108 109 96 97
  | .stws => stShared1 125 126
  | .bar0 => .barSyncN (.reg 127) (.reg 128) true
  | .ldws => ldShared1 281 130
  | .bfb 0 => shflBfly 134 281 135 136 137
  | .bfb 1 => shflBfly 138 139 140 136 137
  | .bfb 2 => shflBfly 141 142 143 136 137
  | .bfb 3 => shflBfly 144 145 146 136 137
  | .bfb _ => shflBfly 147 148 149 136 137
  | .stts => stShared1 150 151
  | .bar1 => .barSyncN (.reg 153) (.reg 154) true
  | .ldts => ldShared1 155 156
  | .ldwa => ldGlobal4 290 167 170 173 176
  | .ldsa0 => ldShared4 161 157 158 159 160
  | .ldsa1 => ldShared4 166 162 163 164 165
  | .stoa => stGlobal4 312 [.reg 211, .reg 212, .reg 213, .reg 214]
  | .ldwb => ldGlobal4 313 225 228 231 234
  | .ldsb0 => ldShared4 219 215 216 217 218
  | .ldsb1 => ldShared4 224 220 221 222 223
  | .stob => stGlobal4 334 [.reg 269, .reg 270, .reg 271, .reg 272]
  | .bar2 => .barSyncN (.reg 273) (.reg 154) true
  | .exit => .ret

/-- **The instruction at a site** is its site instruction, unguarded. -/
theorem code_site {d : D} (hi : Inv P g d) : kernel.code[d.site.pc]? = some ⟨none, siteOp d⟩ := by
  rcases hs : d.site with _ | _ | _ | _ | _ | _ | _ | k | _ | _ | _ | k | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _
  all_goals simp only [siteOp, hs]
  all_goals first
    | exact Flow.code_shfl_0 | exact Flow.code_load_0 | exact Flow.code_store_0
    | exact Flow.code_store_1 | exact Flow.code_load_1 | exact Flow.code_store_2
    | exact Flow.code_store_3 | exact Flow.code_store_4 | exact Flow.code_bar_0
    | exact Flow.code_load_2 | exact Flow.code_store_5 | exact Flow.code_bar_1
    | exact Flow.code_load_3 | exact Flow.code_load_4 | exact Flow.code_load_5
    | exact Flow.code_load_6 | exact Flow.code_store_6 | exact Flow.code_load_7
    | exact Flow.code_load_8 | exact Flow.code_load_9 | exact Flow.code_store_7
    | exact Flow.code_bar_2 | exact Flow.code_exit_0
    | (have hk := hi.bfa _ hs
       interval_cases k
       exacts [Flow.code_shfl_1, Flow.code_shfl_2, Flow.code_shfl_3, Flow.code_shfl_4,
         Flow.code_shfl_5])
    | (have hk := (hi.bfb _ hs).1
       interval_cases k
       exacts [Flow.code_shfl_6, Flow.code_shfl_7, Flow.code_shfl_8, Flow.code_shfl_9,
         Flow.code_shfl_10])

theorem siteOp_event (d : D) : (siteOp d).isLocal = false := by
  unfold siteOp
  split <;> rfl

theorem of_cont {d : D} {e : Event} {u : TState} (h : Cont P L g d e u) :
    ((code P L g).next d e = some none ∨ ∃ d' t', (code P L g).next d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ (code P L g).Good (some d') t') ∨
    ((code P L g).next d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) :=
      by
  rcases h with ⟨d', t', hn, hl, hat, hi⟩ | ⟨hn, hd⟩
  · exact .inl (.inr ⟨d', t', hn, hl, hat, hi⟩)
  · exact .inr ⟨hn, hd⟩

/-- The step of each site. -/
theorem step (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t u : TState} {e : Event}
    {ins : Instr} (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  rcases hs : d.site with _ | _ | _ | _ | _ | _ | _ | k | _ | _ | _ | k | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _
  · exact step_shfl0 hpre hg hs hi h hc hf
  · exact step_ldxa hpre hs hi h hc hf
  · exact step_stxa0 hpre hs hi h hc hf
  · exact step_stxa1 hpre hs hi h hc hf
  · exact step_ldxb hpre hs hi h hc hf
  · exact step_stxb0 hpre hs hi h hc hf
  · exact step_stxb1 hpre hs hi h hc hf
  · have hk := hi.bfa k hs
    interval_cases k
    · exact step_bfa0 hpre hs hi h hc hf
    · exact step_bfa1 hpre hs hi h hc hf
    · exact step_bfa2 hpre hs hi h hc hf
    · exact step_bfa3 hpre hs hi h hc hf
    · exact step_bfa4 hpre hs hi h hc hf
  · exact step_stws hpre hs hi h hc hf
  · exact step_bar0 hpre hs hi h hc hf
  · exact step_ldws hpre hs hi h hc hf
  · have hk := (hi.bfb k hs).1
    interval_cases k
    · exact step_bfb0 hpre hs hi h hc hf
    · exact step_bfb1 hpre hs hi h hc hf
    · exact step_bfb2 hpre hs hi h hc hf
    · exact step_bfb3 hpre hs hi h hc hf
    · exact step_bfb4 hpre hs hi h hc hf
  · exact step_stts hpre hs hi h hc hf
  · exact step_bar1 hpre hs hi h hc hf
  · exact step_ldts hpre hs hi h hc hf
  · exact step_ldwa hpre hs hi h hc hf
  · exact step_ldsa0 hpre hs hi h hc hf
  · exact step_ldsa1 hpre hs hi h hc hf
  · exact step_stoa hpre hs hi h hc hf
  · exact step_ldwb hpre hs hi h hc hf
  · exact step_ldsb0 hpre hs hi h hc hf
  · exact step_ldsb1 hpre hs hi h hc hf
  · exact step_stob hpre hs hi h hc hf
  · exact step_bar2 hpre hs hi h hc hf
  · exfalso
    rw [tmpl_site hpre hi h hc] at hf
    simp only [siteTmpl, hs] at hf
    exact absurd hf.2 (by simp)

/-- **The thread's site machine is sound.** -/
theorem sound (hpre : Pre P L mem0) (hg : g < L.threads) : (code P L g).Sound where
  start := by
    obtain ⟨t, hr, ht⟩ := start (g := g) hpre
    refine ⟨t, hr, atD_of rfl rfl ht, ?_⟩
    show Inv P g ({ site := .shfl0 } : D)
    inv_tac
  steps := by
    intro d
    constructor
    · intro hi
      exact ⟨_, code_site hi, siteOp_event d, trivial⟩
    · intro t e u ins h hi hc hf
      exact of_cont (step hpre hg hi h hc hf)

theorem siteTmpl_ne_ub {d : D} {t : TState} {f : Fault} : siteTmpl P g d t ≠ .ub f := by
  unfold siteTmpl
  split <;> simp

/-- No site has an undefined-behaviour template. -/
theorem tmplOk (hpre : Pre P L mem0) : (code P L g).TmplOk := by
  intro d t ins hat hi hc f
  have h : eventTmpl Prod L g t ins.op = siteTmpl P g d t := tmpl_site hpre hi hat hc
  rw [h]
  exact siteTmpl_ne_ub

end
end PTX.Kernels.RmsNorm.Proof
