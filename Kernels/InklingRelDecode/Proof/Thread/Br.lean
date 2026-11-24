-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiEntry

@[expose] public section

/-! # The bridge from the softmax loop to the epilogue: the registers and the float steps

The default warps run five local instructions between the loop's exit and the epilogue's poll of
`o_final` (pcs 2560-2564, the bridge's first part): the test of `num_iters`
(`setp.lt.s32 %p173, %r25, 1`), the release of the dependent grid
(`griddepcontrol.launch_dependents`), the row's log-sum-exp
(`lg2.approx.ftz.f32 %r1298, %r1454`, then `fma.rn.f32 %r63, %r37, %r1453, %r1298`) and the
parity word of the poll (`mov.b32 %r1299, 0`). None is an event. The poll (pc 2565) is the
epilogue's first site, and the local code after it (the zero pair, the zero test
`setp.equ.f32 %p178, %r1454, 0f0`, the 31 copies of the pair and the branch `@%p173 bra 2674`,
pcs 2567-2600) is the epilogue's (`Epi.p2_run`): the second kernel fix moved the poll in front of
it, so every thread, also one with `num_iters < 1`, polls.

`In` is the state the softmax loop hands over: the registers live at pc 2560, valued as the
epilogue's `Prm` values them (`Epi.Prm`), with the row sum `%r1454` (`l`), the scale `%r37`
(`sc`), the row maximum `%r1453` (`mx`) and `num_iters` `%r25` (`n`) in addition. `valueB i` gives
every register of the bridge its value, independently of the pc: a register the code writes has
there the value of its (only) write, so the facts at every pc of the bridge are the registers live
there valued by `valueB i`.

The float steps are `lg2.approx.ftz.f32` (read as the exact `Real.logb 2` of a finite positive
operand by `Assumptions.lg2Exact`, as Core's table elsewhere: `lg2E`) and `fma.rn.f32` (exact real
arithmetic by `Assumptions.idealArith`: `floatE`). `exec_lg2E` and `exec_floatE_fma_at` are their
local steps; the epilogue's `Prm` is `prm i`. The zero test is the epilogue's step
(`Epi.Prm.eq0`, `Epi.Prm.setpOk`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Br
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Epi

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-! ### The state the softmax loop hands over -/

/-- The registers live at pc 2560 (decoder ids: `%rK` is `461 + K`, `%rdK` is `1948 + K`, `%pK` is
`K`): the epilogue's inherited registers (`Epi.Prm`), the row sum `%r1454` (`l`), `%r37` (`sc`, the
scale of the log-sum-exp), `%r1453` (`mx`, the row maximum) and `%r25` (`n`, `num_iters`). -/
structure In where
  p3 : Bool
  rv : Bool
  tid : Nat
  tm : Nat
  w : Nat
  c0 : Nat
  mb : Nat
  a : Nat
  b : Nat
  c : Nat
  dd : Nat
  e : Nat
  d0 : Nat
  ob : Nat
  lb : Nat
  l : Value
  sc : Value
  mx : Value
  n : Nat

/-- The numbers are the 32-bit and 64-bit numbers the registers hold, as in `Epi.Prm.Ok`; the
row sum is an `f32` word. -/
structure In.Ok (i : In) : Prop where
  tid : i.tid < M32
  tm : i.tm < M32
  w : i.w < 4
  c0 : i.c0 < M32
  mb : i.mb < M32
  a : i.a < M32
  b : i.b < M32
  c : i.c < M32
  dd : i.dd < M32
  e : i.e < M32
  n : i.n < M32
  d0 : i.d0 < M64
  ob : i.ob < M64
  lb : i.lb < M64
  row : ((((i.a * i.b + i.c) % M32 + i.dd) % M32) * 12 + i.e) % M32 < 2 ^ 24
  l : i.l.bytes = 4
  /-- The barrier is 8-aligned and the two pointers are aligned to the 4 bytes of an `f32`. -/
  mb8 : i.mb % 8 = 0
  ob4 : i.ob % 4 = 0
  lb4 : i.lb % 4 = 0
  /-- The column base of the load of `O` leaves room for its 256 columns. -/
  c0col : i.c0 + 256 ≤ 2 ^ 16

/-! ### The float outcomes -/

/-- `lg2.approx.ftz.f32`. -/
abbrev lg2I : FloatInstr :=
  { op := .lg2, ty := ty1 .f32, mode := .approx, ftz := true, dsts := [], srcs := [] }

/-- **The outcome of `lg2.approx.ftz.f32` at pc 2562** (`Assumptions.lg2Exact`): the exact
`Real.logb 2` of a finite positive operand, the Core table's value (zero and infinite operands,
`coreFloat`) elsewhere. -/
def lg2E (v : Value) : Exec Value :=
  match readEReal .f32 v with
  | none => coreFloat lg2I [v]
  | some (.error f) => .error f
  | some (.ok x) =>
    if 0 < x ∧ x ≠ ⊤ then .ok (.float .f32 (Real.logb 2 x.toReal)) else coreFloat lg2I [v]

/-- `fma.rn.f32` of the log-sum-exp. -/
abbrev lseI : FloatInstr := fmaI .rn false

/-- The value of `%r1298`, the logarithm of the row sum. -/
def In.lg2v (i : In) : Value := okVal (b32 0) (lg2E i.l)

/-- The value of `%r63`, the log-sum-exp `fma(scale, max, log2 l)`. -/
def In.lse (i : In) : Value := okVal (b32 0) (floatE lseI [i.sc, i.mx, i.lg2v])

/-- The value of `%p178` (`Epi.Prm.eq0`, computed by the epilogue after the poll). -/
def In.eq0 (i : In) : Bool :=
  match setpE (.unord .eq) false i.l zero32 with
  | .ok b => b
  | .error _ => false

/-- The value of `%p173`: `num_iters < 1` as a signed 32-bit comparison. -/
def In.skip (i : In) : Bool := decide (toSigned 32 (BitVec.ofNat 64 i.n) < 1)

/-- The bridge's first part does not fault: `lg2` and `fma` have outcomes. (The zero test
`setp.equ` is after the poll, in the epilogue: `Epi.Prm.setpOk`.) -/
def In.NoFault (i : In) : Prop :=
  (lg2E i.l).toBool = true ∧ (floatE lseI [i.sc, i.mx, i.lg2v]).toBool = true

/-- **The epilogue's `Prm` of the state**: the inherited registers, the row sum and the
log-sum-exp. -/
def prm (i : In) : Prm where
  p3 := i.p3
  rv := i.rv
  tid := i.tid
  tm := i.tm
  w := i.w
  c0 := i.c0
  mb := i.mb
  a := i.a
  b := i.b
  c := i.c
  dd := i.dd
  e := i.e
  d0 := i.d0
  ob := i.ob
  lb := i.lb
  l := i.l
  lse := i.lse

/-! ### The register table -/

/-- The registers of the bridge's first part: id, value. -/
def In.scalars (i : In) : List (Nat × Value) :=
  [ (3, .pred i.p3), (175, .pred i.rv), (462, b32 i.tid), (463, b32 i.tm), (464, b32 i.w),
    (478, b32 i.b), (486, b32 i.n), (491, b32 i.c0), (496, b32 i.c), (497, b32 i.e),
    (498, i.sc), (524, i.lse), (533, b32 i.a), (610, b32 i.dd), (624, b32 i.mb),
    (1759, i.lg2v), (1760, zero32), (1914, i.mx), (1915, i.l), (1956, b64 i.d0),
    (2023, b64 i.ob), (2024, b64 i.lb), (173, .pred i.skip) ]

/-- The register table. -/
abbrev In.table (i : In) : List (Nat × Value) := i.scalars

/-- The value of every register of the bridge. -/
def valueB (i : In) (r : Nat) : Value := ((i.table).lookup r).getD (b32 0)

/-- The facts at a pc of the bridge: the registers live there, valued by `valueB`. -/
def bfacts (pc : Nat) (i : In) : List (Nat × Value) := Flow.factsFrom (Flow.live pc) (valueB i)

/-- **The facts the softmax loop must provide at pc 2560.** -/
abbrev exitFacts (i : In) : List (Nat × Value) := bfacts 2560 i

/-- The value-table reduction used after evaluating a segment. -/
macro "br_values" : tactic =>
  `(tactic| simp only [valueB, In.scalars, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none,
    Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, and_self, and_false, false_and, ↓reduceIte])

/-- Evaluate a segment from `h` and close the facts of its end state. -/
syntax "br_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| br_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      seg_fp $h using
        try br_values
        all_goals seg_close [$extra,*]))

/-- `br_seg` for segments with signed integer arithmetic or comparisons. -/
syntax "br_segs " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| br_segs $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      seg_fp $h using
        try br_values
        all_goals first
          | seg_close [$extra,*]
          | (show Value.bits _ _ = _; norm_signed [intOf, intBits, eq_self, $extra,*])
          | (show Value.pred _ = _; norm_signed [intOf, intBits, eq_self, $extra,*])))

end
end PTX.Kernels.InklingRelDecode.Proof.Br
