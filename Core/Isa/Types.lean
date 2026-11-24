-- SPDX-License-Identifier: Apache-2.0
module


@[expose] public section

/-!
# Instruction data types

The qualifier vocabulary the instruction families share: data types, comparison operators, state
spaces, memory semantics and scopes.
-/

namespace PTX

/-! ## PROG-ISA-TYPES — data types and shared qualifiers
Statement: An instruction's data type is a predicate, an integer type of a kind and a width, a
  floating-point type, or a packed type of several elements. State spaces, memory semantics,
  comparison operators and scopes are the qualifiers the manual lists for them, and `FloatFmt` is
  the set of floating formats whose payloads the model represents as numbers.

Defs: FloatFmt, FloatFmt.bytes, FloatRound, Space, IType, Cmp, MbarScope, FType, FType.fmt?, DType,
  DType.width, DType.kind?, SharedWindow, StateSpace, Sem, BoolOp

Source:
- §5.2.1: "Fundamental Type Specifiers"
- §5.2.5 (packed data types)
- §9.3.1.1 (Table 23, integer comparison operators): "eq, ne, lt, le, gt, ge"
- §9.3.1.1 (Table 23, integer comparison operators): "lo, ls, hi, hs"
- §5.1 (state spaces)
- §8.4 (memory operation qualifiers)
- §9.7.7.2 (setp `.BoolOp`)

Direction: representation

Applies: The qualifier values of every decoded instruction

Premises: The value is one the instruction's syntax lists.

Effect: Representation only; the rules of each family read these values.
  `DType.int k w` is `.b<w>`, `.u<w>` or `.s<w>`; `DType.packed e n` is the packed type of `n`
  elements of type `e` (`.f16x2` is `packed (float f16) 2`). `FType` lists every floating type name
  of an instruction; `FType.fmt?` gives the payload format of the model (THREAD-BITS), which exists
  for `.f16`, `.bf16`, `.f32`, `.f64`, `.e4m3` and `.e5m2` only.
-/

/-- A floating-point format of a data type: `f16`, `bf16`, `f32`, `f64`, `e4m3` or `e5m2`. -/
inductive FloatFmt where
  | f16 | bf16 | f32 | f64 | e4m3 | e5m2
  deriving DecidableEq, Repr

def FloatFmt.bytes : FloatFmt → Nat
  | .f16 | .bf16 => 2
  | .f32 => 4
  | .f64 => 8
  | .e4m3 | .e5m2 => 1

/-- The rounding modifier `.rnd` of a floating instruction (§9.7.3): to nearest even, toward
zero, toward negative infinity, toward positive infinity. -/
inductive FloatRound where
  | rn | rz | rm | rp
  deriving DecidableEq, Repr

/-- State spaces of memory locations in this model: global, shared, a thread's local memory and
constant memory. -/
inductive Space where
  | global | shared | «local» | const
  deriving DecidableEq, Repr

/-- Integer interpretation of an instruction type. -/
inductive IType where
  | b | u | s
  deriving DecidableEq, Repr

/-- A comparison operator (§9.3.1.1, Table 23): the signed or untyped ones and the unsigned ones
`lo`, `ls`, `hi`, `hs`. -/
inductive Cmp where
  | eq | ne | lt | le | gt | ge | lo | ls | hi | hs
  deriving DecidableEq, Repr

/-- The scope of a strong operation (§8.5, Table 21): `.cta`, `.cluster`, `.gpu` or `.sys`. It is
distinct from an object's shared address qualifier. -/
inductive MbarScope where
  | cta | cluster | gpu | sys
  deriving DecidableEq, Repr

/-- The floating-point type names of instruction types. -/
inductive FType where
  | f16 | bf16 | tf32 | f32 | f64 | e4m3 | e5m2 | e2m3 | e3m2 | e2m1 | ue8m0 | ue5m3 | s2f6
  deriving DecidableEq, Repr

/-- The payload format of a floating type, where the model has one. -/
def FType.fmt? : FType → Option FloatFmt
  | .f16 => some .f16
  | .bf16 => some .bf16
  | .f32 => some .f32
  | .f64 => some .f64
  | .e4m3 => some .e4m3
  | .e5m2 => some .e5m2
  | _ => none

/-- A data type of an instruction. -/
inductive DType where
  | pred
  | int (k : IType) (w : Nat)
  | float (f : FType)
  | packed (e : DType) (n : Nat)
  deriving DecidableEq, Repr

/-- The width in bits of a data type; 1 for `.pred`. -/
def DType.width : DType → Nat
  | .pred => 1
  | .int _ w => w
  | .float f => match f with
    | .f16 | .bf16 => 16
    | .tf32 | .f32 => 32
    | .f64 => 64
    | .e4m3 | .e5m2 | .ue8m0 => 8
    | .e2m3 | .e3m2 | .s2f6 => 8
    | .e2m1 => 4
    | .ue5m3 => 8
  | .packed e n => e.width * n

/-- The integer kind of an integer type. -/
def DType.kind? : DType → Option IType
  | .int k _ => some k
  | _ => none

/-- The window of a `.shared` qualifier: `::cta` (also written `.shared` alone) or `::cluster`. -/
inductive SharedWindow where
  | cta | cluster
  deriving DecidableEq, Repr

/-- The state-space qualifier of a memory instruction (§5.1): `param` is the kernel parameter
space (`.param::entry`) and `paramFunc` the device function parameter space (`.param::func`). -/
inductive StateSpace where
  | global
  | shared (w : SharedWindow)
  | param
  | paramFunc
  | «local»
  | const
  deriving DecidableEq, Repr

/-- The memory semantics of an access (§8.4): `.weak` (also when absent on `ld`/`st`),
`.relaxed`, `.acquire`, `.release`, `.acq_rel` or `.volatile`. The `.mmio` qualifier is a separate
flag of the access (`MemAccess.mmio`) and keeps the access's `.sem`. -/
inductive Sem where
  | weak | relaxed | acquire | release | acqRel | volatile
  deriving DecidableEq, Repr

/-- The `.BoolOp` combining a comparison with a predicate (§9.7.7.1, §9.7.7.2). -/
inductive BoolOp where
  | and | or | xor
  deriving DecidableEq, Repr

end PTX
