-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Data.Decoded
public import Tactics.KernelRfl

@[expose] public section

/-! Static pipeline schedule of the production kernel, read from the decoded instructions.
Each `mbarrier.try_wait.parity` is resolved to its barrier (`v_ptr + offset`) and to the
instruction that defines its parity operand. This is the code-level premise of
`MBarrier.Alternates`: the producer polls `empty[s]` with literal parities 1 then 0 per
round, the MMA thread polls `full[s]` with one register toggled once per round. -/
namespace PTX.Kernels.Fp16Gemm8192.Pipeline
open PTX

/-- The register an instruction of these forms writes: an integer, move, conversion, load or
address instruction with a single destination register. -/
def dst? : Op → Option Nat
  | .int ⟨_, _, _, [some d], _⟩ | .move ⟨_, _, [some d], _⟩ | .cvt { d := d, .. }
  | .mem { kind := .load, dsts := [some d], .. } | .addr (.cvta _ _ _ d _)
  | .addr (.mapa _ _ d _ _) => some d
  | _ => none

/-- The last instruction before `pc` that writes `r`, with its index. -/
def lastDef (code : List Instr) (pc : Nat) (r : Nat) : Option (Nat × Op) :=
  ((List.range pc).reverse.find? fun k =>
    match code[k]? with
    | some ins => dst? ins.op == some r
    | none => false).bind fun k => (code[k]?).map fun ins => (k, ins.op)

/-- Every instruction writing `r`. -/
def writers (code : List Instr) (r : Nat) : List (Nat × Op) :=
  code.zipIdx.filterMap fun (ins, k) =>
    if dst? ins.op == some r then some (k, ins.op) else none

/-- A barrier operand `base + 0` whose only writer is `v_ptr + offset`, where the `v_ptr`
register's only writer is the shared window's start. -/
def barrierOffset (code : List Instr) (base : Nat) : Option Int :=
  match writers code base with
  | [(_, .int ⟨.add, .int _ 32, false, [some _], [.reg vp, .imm off]⟩)] =>
    match writers code vp with
    | [(_, .move ⟨.scalar, .int _ 32, [some _], [.sharedSym 0]⟩)] => some off
    | _ => none
  | _ => none

/-- A parity operand: a literal when its register's only writer in the whole kernel is a
`mov` of that literal (so no path can reach the wait with another value), otherwise the
loop-carried register itself. -/
inductive Parity where
  | literal (value : Int)
  | register (r : Nat)
  deriving DecidableEq, Repr

def parityOf (code : List Instr) : Opnd → Option Parity
  | .imm v => some (.literal v)
  | .reg r =>
    match writers code r with
    | [(_, .move ⟨.scalar, .int _ 32, [some _], [.imm v]⟩)] => some (.literal v)
    | _ => some (.register r)
  | _ => none

/-- All waits: program counter, barrier offset from `v_ptr`, parity. -/
def waits (code : List Instr) : List (Nat × Option Int × Option Parity) :=
  code.zipIdx.filterMap fun (ins, pc) =>
    match ins.op with
    | Op.mbarWait _ base 0 parity _ _ =>
      some (pc, barrierOffset code base, parityOf code parity)
    | _ => none

/-- Every wait of the production kernel. -/
theorem schedule : waits Decoded.kernel.code = [
    (119, some 40, some (.literal 1)), (149, some 48, some (.literal 1)),
    (178, some 56, some (.literal 1)), (207, some 64, some (.literal 1)),
    (236, some 40, some (.literal 0)), (264, some 48, some (.literal 0)),
    (292, some 56, some (.literal 0)), (320, some 64, some (.literal 0)),
    (350, some 104, some (.register 876)),
    (389, some 40, some (.literal 1)), (393, some 48, some (.literal 1)),
    (397, some 56, some (.literal 1)), (401, some 64, some (.literal 1)),
      (419, some 128, some (.register 881)),
    (431, some 104, some (.register 880)), (494, some 104, some (.register 883)),
    (513, none, some (.register 882)),
    (520, some 8, some (.register 885)), (541, some 16, some (.register 885)),
    (563, some 24, some (.register 885)), (585, some 32, some (.register 885)),
    (707, some 104, some (.register 889)), (746, none, some (.register 890))] := by
  kernel_rfl

def isMovImm (r : Nat) (v : Int) : Op → Bool
  | .move ⟨.scalar, .int _ 32, [some d], [.imm x]⟩ => d == r && x == v
  | _ => false

def isToggle (r : Nat) : Op → Bool
  | .int ⟨.xor, .int .b 32, false, [some d], [.reg x, .imm 1]⟩ => d == r && x == r
  | _ => false

/-- A loop-carried parity: one `mov r, 0` at `init`, one `xor r, r, 1` at `toggle`, and
no other writer anywhere in the kernel. -/
def TogglesOnly (code : List Instr) (r : Nat) (init toggle : Nat) : Bool :=
  match writers code r with
  | [(i, a), (j, b)] => i == init && j == toggle && isMovImm r 0 a && isToggle r b
  | _ => false

/-- The MMA thread's full-barrier parity starts at 0; its only other writer is a toggle. -/
theorem full_parity : TogglesOnly Decoded.kernel.code 885 484 606 = true := by
  kernel_rfl

/-- The other loop-carried parities have the same shape. -/
theorem loop_parities :
    TogglesOnly Decoded.kernel.code 876 110 383 = true := by
  kernel_rfl

/-- All branches, as (source, target). -/
def branches (code : List Instr) : List (Nat × Nat) :=
  code.zipIdx.filterMap fun (ins, k) =>
    match ins.op with
    | Op.bra t _ => some (k, t)
    | _ => none

def isRet (code : List Instr) (k : Nat) : Bool :=
  match (code[k]?).map Instr.op with
  | some Op.ret => true
  | _ => false

/-- `[lo, hi]` is a single-entry round: no branch enters it except at `lo`, no `ret` is in
it, and inside it the only branches are the back edge `hi → lo`, two-instruction wait
spins, and forward skips of at most three instructions. Every iteration therefore runs
every non-skipped instruction of the round once, in order. -/
def RoundLoop (code : List Instr) (lo hi : Nat) : Bool :=
  (branches code).all (fun (k, t) =>
    if (lo < t && t ≤ hi) || (lo ≤ k && k ≤ hi) then
      (lo ≤ k && k ≤ hi && lo ≤ t && t ≤ hi && t ≤ k + 3 && k ≤ t + 2) || (k == hi && t == lo)
    else true) &&
  ((List.range (hi + 1 - lo)).all fun i => !isRet code (lo + i))

/-- No branch at or after `init` returns to it or before it: an initialization at `init`
runs once, before every later loop. -/
def RunsOnce (code : List Instr) (init : Nat) : Bool :=
  (branches code).all fun (k, t) => k < init || init < t

/-- The MMA thread's round (pcs 517–609): waits on `full[0..3]` at 520, 541, 563, 585, then
the parity toggle at 606, before the back edge. The parity's initialization (484) runs once,
so the toggles accumulate across output tiles. These are the static facts behind the
dynamic claim that the `c`-th wait on a stage uses parity `c % 2` (`Alternates … 0`). -/
theorem mma_round : RoundLoop Decoded.kernel.code 517 609 = true := by
  kernel_rfl

theorem full_parity_init_once : RunsOnce Decoded.kernel.code 484 = true := by
  kernel_rfl

/-- The producer's round (pcs 115–346) waits on `empty[0..3]` with parity 1, then again
with parity 0, each once per iteration (`schedule`). These are the static facts behind the
dynamic claim that the `c`-th wait on a stage uses parity `(c + 1) % 2` (`Alternates … 1`). -/
theorem producer_round : RoundLoop Decoded.kernel.code 115 346 = true := by
  kernel_rfl

end PTX.Kernels.Fp16Gemm8192.Pipeline
