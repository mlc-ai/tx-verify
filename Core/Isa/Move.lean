-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Operand
public import Core.Isa.Rule

@[expose] public section

/-!
# Register moves

`mov` of a scalar, and the packing and unpacking forms of `mov`.
-/

namespace PTX

/-! ## PROG-ISA-MOVE — register moves
Statement: A move is a scalar `mov`, a packing `mov` that joins source elements into one register,
  or an unpacking `mov` that splits one register into destination elements, with its data type,
  destinations and sources. Every entry of the `move` family decodes to it.

Defs: MoveKind, MoveInstr, Decode.MoveInstr.ofRaw, MoveInstr.rule

Source:
- §9.7.10.3: "mov.type d, a;"
- §9.7.10.3: ".type = { .pred, .b16, .b32, .b64, .u16, .u32, .u64, .s16, .s32, .s64, .f32, .f64 };"
- §9.7.10.4: "mov.type d, a; .type = { .b16, .b32, .b64, .b128 };"
- §9.7.10.4: "pack two 16-bit elements into .b32 d = a.x | (a.y << 16)"
- §9.7.10.4: "When destination operand d is a vector register, the sink symbol '_' may be used for
    one or more elements provided that at least one element is a scalar register."

Direction: representation

Applies: Every instruction of the `move` family

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at the
  widths of the operand types.

Effect: Representation; `MoveInstr.rule` selects THREAD-MOVE for the scalar moves of every type of
  the syntax, and for the packing and unpacking of two or four elements, and no rule otherwise.
  The type of a pack or unpack is the type of the whole register (`.b32` for `{.b16, .b16}`). A
  destination of an unpack may be the sink `_`, and an unpack whose destinations are all sinks is
  rejected; the named destinations are distinct (§6.4.3).
-/

/-- Which `mov` form an instruction is. -/
inductive MoveKind where
  | scalar | pack | unpack
  deriving DecidableEq, Repr

/-- A register move: its form, the type of the whole value, destinations (`none` for `_`) and
sources (the elements of a pack, low first). -/
structure MoveInstr where
  kind : MoveKind
  ty : DType
  dsts : List (Option Nat)
  srcs : List Opnd
  deriving DecidableEq, Repr

namespace Decode

/-- The `move`-family instruction of a recognized instruction. -/
def MoveInstr.ofRaw (env : Env) (r : Isa.Raw) : M MoveInstr := do
  let ty ← dtype (r.get .type)
  let kind : MoveKind := match r.entry with
    | .mov => .scalar
    | .mov_pack_b16x2 | .mov_pack_b32x2 | .mov_pack_b16x4 | .mov_pack_b64x2
    | .mov_pack_b32x4 => .pack
    | _ => .unpack
  let (dsts, srcs) ← match kind, ty, r.opnds with
    | .scalar, .int .b 64, [d, ⟨_, _, _, _, _, .symbol name⟩] =>
      match env.locals.lookup name with
      | some offset => pure (← rdsts env d, [.localSym offset])
      | none => operands env r
    | _, _, _ => operands env r
  if kind == .unpack && dsts.all (·.isNone) then throw "unpack without a destination register"
  return { kind, ty, dsts, srcs }

end Decode

/-- The rule of a move: THREAD-MOVE for a scalar move of `.pred`, of the `.b`, `.u`, `.s` types of
16 to 64 bits, `.f32` or `.f64`, and for a pack or unpack of two or four elements of 8 to 64 bits
into `.b16`, `.b32`, `.b64` or `.b128`, with at least one destination register. -/
def MoveInstr.rule (m : MoveInstr) : Option RuleId :=
  let scalar : Bool := match m.ty with
    | .pred => true
    | .int _ w => [16, 32, 64].contains w
    | .float .f32 | .float .f64 => true
    | _ => false
  -- `n` elements of 8, 16, 32 or 64 bits make up the whole `.b` register
  let elems (n : Nat) : Bool := match m.ty with
    | .int .b w => [(16, 2), (32, 2), (32, 4), (64, 2), (64, 4), (128, 2), (128, 4)].contains (w, n)
    | _ => false
  match m.kind, m.dsts, m.srcs with
  | .scalar, [some _], [_] => if scalar then some .threadMove else none
  | .pack, [some _], as => if elems as.length then some .threadMove else none
  | .unpack, ds, [_] =>
    if elems ds.length && ds.any (·.isSome) then some .threadMove else none
  | _, _, _ => none

end PTX
