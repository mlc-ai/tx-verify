-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Isa.Types
public import Core.Isa.SReg

@[expose] public section

/-!
# Operands

The typed operands of an instruction and their resolution from the source spelling: literals,
declared registers, special registers and the addresses of `.shared` variables and parameters.
The instruction families (`Core/Isa/`) resolve the operands of a recognized instruction
(`Isa.Raw`) with these functions; `Core/Source/Decode.lean` builds the environment.
-/

/-! ## PROG-OPERAND — operands and their resolution
Statement: An operand is a register, an integer or binary32 literal, a special register, the address
  of a `.shared` variable or the address of a kernel parameter. A register operand must be declared
  with the width the instruction expects, a literal is read with its §4.5.1 type, and a special
  register has the width of its declared type. A `.pred` source is a predicate register, the
  `.pred` special register `%is_explicit_cluster`, or an integer constant (§4.5.3: "zero values
  are False and non-zero values are True"). A `%perctamemory` register is an operand only in
  a kernel with a `.minperctamemory` directive.

Defs: *

Source:
- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "Integer constants are 64-bits in
    size and are either signed or unsigned, i.e., every integer constant has type .s64 or .u64"
- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "Integer literals may be followed
    immediately by the letter U to indicate that the literal is unsigned."
- §4.5.5: "Unary plus and minus preserve the type of the input operand."
- §4.5.2 (0f binary32 constants)
- §9.4 Table 26 (an `.sX`/`.uX` operand of an `.fX` instruction type is): "invalid"
- §6.4.3: "when specified as destination operand, all elements in vector expression must be unique,
    otherwise behavior is undefined"
- §9.3: "predicate registers can be declared as .reg .pred p, q, r;"
- §10.11: ".sreg .pred %is_explicit_cluster;"
- §11.5.10: "Only entry functions specifying this directive are allowed to use special registers
    %perctamemoryoffset or %perctamemorysize ."
- §6.4.1: "[var+immOff] a sum of address of addressable variable var containing a byte address plus
    a constant integer byte offset (signed, 32-bit)."
- §4.5.3: "For predicate-type data initializers and instruction operands, integer constants are
    interpreted as in C, i.e., zero values are False and non-zero values are True ."

Direction: stricter

Effect: The literal rules, register numbering and rejections are those PROG-DECODE states; this
  file holds the functions that apply them to one operand.
-/

namespace PTX

/-- A source operand of an instruction: a register, an integer or binary32 literal, a special
register, or the address of a `.shared` variable, `.local` variable or kernel parameter. -/
inductive Opnd where
  /-- A register, by its id: its index in the kernel's declared-register order
  (`Kernel.regNames`). -/
  | reg (r : Nat)
  | imm (value : Int)
  /-- A `0fXXXXXXXX` literal: raw binary32 pattern, decoded exactly. -/
  | f32imm (bits : Nat)
  | sreg (s : SReg)
  /-- Address of a `.shared` variable: the launch's shared window base plus `offset`. -/
  | sharedSym (offset : Nat)
  /-- Address of a `.local` variable: the launch's local base plus `offset`. -/
  | localSym (offset : Nat)
  /-- Address of a kernel parameter object, not the value stored in it. -/
  | paramSym (name : String)
  deriving DecidableEq, Repr

/-- An addressable by-value kernel parameter object. This records storage, not a
pointer value loaded from that storage. Array element count and alignment are kept
for launch/address validation; no address or host contents are invented here. -/
structure ParamObjectDecl where
  name : String
  elementBits : Nat
  count : Nat
  alignment : Nat
  deriving DecidableEq, Repr

def ParamObjectDecl.bytes (p : ParamObjectDecl) : Nat := p.elementBits / 8 * p.count

namespace Decode
open PTX.Syntax

abbrev M := Except String

def digit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat) else none

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def digits (base : Nat) (d : Char → Option Nat) : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc => d c >>= fun v => digits base d cs (acc * base + v)

def octDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '7' then some (c.toNat - '0'.toNat) else none

def binDigit? (c : Char) : Option Nat :=
  if c = '0' then some 0 else if c = '1' then some 1 else none

/-- §4.5.1: `0[xX]` hexadecimal, `0[bB]` binary, a leading `0` octal, otherwise decimal. -/
def natLit? : List Char → Option Nat
  | [] => none
  | '0' :: 'x' :: cs | '0' :: 'X' :: cs => if cs = [] then none else digits 16 hexDigit? cs 0
  | '0' :: 'b' :: cs | '0' :: 'B' :: cs => if cs = [] then none else digits 2 binDigit? cs 0
  | '0' :: cs => digits 8 octDigit? cs 0
  | cs => digits 10 digit? cs 0

/-- An integer literal (§4.5.1): its value and whether its type is `.u64` — it has the `U`
suffix, or its value is not representable in `.s64`; otherwise it is `.s64`. A value not
representable in `.u64` is not a literal. -/
def intLit (text : String) (cs : List Char) : M (Nat × Bool) := do
  let (body, suffix) := if cs.getLast? = some 'U' then (cs.dropLast, true) else (cs, false)
  let some v := natLit? body | throw s!"bad literal {text}"
  unless v < 18446744073709551616 do throw s!"literal outside 64 bits {text}"
  pure (v, suffix || decide (9223372036854775808 ≤ v))

/-- Literal operand. `0f` + 8 hex digits is binary32. An integer constant is an integer literal
or one unary minus applied to one (§4.5.5: "Unary plus and minus preserve the type of the input
operand."): an `.s64` literal is negated as an integer, a `.u64` literal modulo `2^64`. The
operand holds the constant's value, in `[-2^63, 2^63)` for `.s64` and `[0, 2^64)` for `.u64`. -/
def literal (text : String) : M Opnd :=
  match text.toList with
  | '0' :: 'f' :: cs | '0' :: 'F' :: cs =>
    if cs.length = 8 then
      match digits 16 hexDigit? cs 0 with
      | some v => pure (.f32imm v)
      | none => throw s!"bad float literal {text}"
    else throw s!"unsupported float literal {text}"
  | '-' :: cs => do
    let (v, unsigned) ← intLit text cs
    pure (.imm (if unsigned then ((18446744073709551616 - v) % 18446744073709551616 : Nat)
      else -(v : Int)))
  | cs => do
    let (v, _) ← intLit text cs
    pure (.imm v)

/-- Register class declared by `.reg .<type> %prefix<count>`. -/
structure RegClass where
  pre : List Char
  /-- Count zero denotes one scalar register whose exact name is `pre`. -/
  count : Nat
  /-- 1 for predicates. -/
  width : Nat
  deriving Repr

def typeWidth : String → Option Nat
  | "pred" => some 1
  | "b8" | "u8" | "s8" => some 8
  | "b16" | "u16" | "s16" | "f16" | "bf16" => some 16
  | "b32" | "u32" | "s32" | "f32" => some 32
  | "b64" | "u64" | "s64" | "f64" => some 64
  | "b128" => some 128
  | _ => none

/-- The names of a comma list `a , b , …` of at least two plain names. -/
def commaNames : List String → Option (List String)
  | [a, ",", b] => if a = "," ∨ b = "," then none else some [a, b]
  | a :: "," :: rest => if a = "," then none else (a :: ·) <$> commaNames rest
  | _ => none

/-- The register classes a `.reg` declaration declares, in source order: one name, a
parameterized name `pre<n>`, or a comma list of names `.reg .t a, b, …` (each one register). -/
def regClass : List String → M (List RegClass)
  | [".reg", ty, pre, "<", n, ">"] => do
    let some w := typeWidth (String.ofList (ty.toList.drop 1)) | throw s!"register type {ty}"
    let some c := natLit? n.toList | throw s!"register count {n}"
    unless ty.toList.head? = some '.' ∧ 0 < c do throw s!"register declaration {pre}"
    pure [⟨pre.toList, c, w⟩]
  | ".reg" :: ty :: names => do
    let some w := typeWidth (String.ofList (ty.toList.drop 1)) | throw s!"register type {ty}"
    unless ty.toList.head? = some '.' do throw s!"register type {ty}"
    let ns ← match names with
      | [name] => pure [name]
      | _ => match commaNames names with
        | some ns => pure ns
        | none => throw s!"unsupported declaration {".reg" :: ty :: names}"
    pure (ns.map fun n => ⟨n.toList, 0, w⟩)
  | ts => throw s!"unsupported declaration {ts}"

def stripPrefix : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p = c then stripPrefix ps cs else none

/-- Canonical decimal index: digits without a leading zero, except `0` itself. -/
def canonIndex? : List Char → Option Nat
  | [] => none
  | ['0'] => some 0
  | '0' :: _ => none
  | cs => digits 10 digit? cs 0

/-- The number of names a class declares. -/
def RegClass.size (c : RegClass) : Nat := if c.count = 0 then 1 else c.count

/-- The decimal digits of `n`, prepended to `acc` (fuel: one step per digit). -/
def decimalAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc := Char.ofNat (n % 10 + '0'.toNat) :: acc
    if n < 10 then acc else decimalAux fuel (n / 10) acc

/-- The names a class declares, in index order. -/
def RegClass.names (c : RegClass) : List String :=
  if c.count = 0 then [String.ofList c.pre]
  else (List.range c.count).map fun i => String.ofList (c.pre ++ decimalAux (i + 1) i [])

/-- The index of `r` among the names `c` declares. -/
def RegClass.index? (c : RegClass) (r : List Char) : Option Nat :=
  if c.count = 0 then (if c.pre = r then some 0 else none)
  else match stripPrefix c.pre r with
    | some rest => match canonIndex? rest with
      | some i => if i < c.count then some i else none
      | none => none
    | none => none

/-- Width and id of `r` in each class that declares it; `base` is the id of the first name
of the first class. -/
def regMatches : List RegClass → Nat → List Char → List (Nat × Nat)
  | [], _, _ => []
  | c :: cs, base, r =>
    (match c.index? r with | some i => [(c.width, base + i)] | none => []) ++
      regMatches cs (base + c.size) r

/-- Width and id of a declared register. -/
def regInfo (classes : List RegClass) (r : String) : M (Nat × Nat) :=
  match regMatches classes 0 r.toList with
  | [x] => pure x
  | _ => throw s!"undeclared or ambiguous register {r}"

def regWidth (classes : List RegClass) (r : String) : M Nat :=
  (·.1) <$> regInfo classes r

/-- The decoding environment of a kernel: register classes, labels, scalar parameters with their
widths, `.shared` variables with their offsets, parameter objects, branch tables and `.local` and
`.const` variables with their offsets. -/
structure Env where
  classes : List RegClass
  labels : List (String × Nat)
  params : List (String × Nat)
  /-- `.shared` variables and their byte offsets in the CTA's shared window. -/
  shared : List (String × Nat) := []
  /-- By-value parameter objects (also listed in `params` with their size in bits). -/
  objects : List ParamObjectDecl := []
  /-- `.branchtargets` tables: name, the index of the next instruction, target indices. -/
  tables : List (String × Nat × List Nat) := []
  /-- The index of the instruction being decoded. -/
  pc : Nat := 0
  /-- The kernel has a `.minperctamemory` directive, so the `%perctamemory` registers are
  operands (§11.5.10). -/
  perCtaMemory : Bool := false
  /-- `.local` variables and their byte offsets from the local base (EXT-LOCAL-CONST-LAYOUT). -/
  locals : List (String × Nat) := []
  /-- `.const` variables and their byte offsets from the constant base (EXT-LOCAL-CONST-LAYOUT). -/
  consts : List (String × Nat) := []

/-- Whether a name is a declared predicate register (the grammar's `isPred` oracle). -/
def Env.isPred (env : Env) (r : String) : Bool :=
  match regInfo env.classes r with
  | .ok (1, _) => true
  | _ => false

/-- The id of a register of exactly the given width. -/
def reg (env : Env) (width : Nat) : Operand → M Nat
  | .register r => do
    let (w, i) ← regInfo env.classes r
    unless w = width do throw s!"register {r} has width {w}, expected {width}"
    pure i
  | o => throw s!"expected register, got {repr o}"

/-- A special register is an operand of the kernel: a `%perctamemory` register needs the
kernel's `.minperctamemory` directive (§11.5.10). -/
def Env.sregAllowed (env : Env) (r : String) (s : SReg) : M Unit :=
  if s.perCtaMemory && !env.perCtaMemory then throw s!"{r} without .minperctamemory"
  else pure ()

/-- A source operand of the given width: register, literal, special register of that width, or
the address of a `.shared` variable (32 bits) or of a parameter (32 or 64 bits). -/
def src (env : Env) (width : Nat) : Operand → M Opnd
  | .register r => match SReg.ofName? r with
    | some s => do
      env.sregAllowed r s
      if s.width = width then pure (.sreg s) else throw s!"{r} is {s.width}-bit"
    | none => .reg <$> reg env width (.register r)
  | .literal t => do
    let o ← literal t
    match o with
    | .f32imm _ => if width = 32 then pure o else throw s!"{t} is 32-bit"
    | _ => if width ≤ 64 then pure o else throw s!"{t}: integer constants are 64-bit"
  | .symbol name => match env.shared.lookup name with
    | some off =>
      if width = 32 then pure (.sharedSym off) else throw s!"{name}: 32-bit shared address"
    | none =>
      if (env.params.lookup name).isSome then
        if width = 32 ∨ width = 64 then pure (.paramSym name)
        else throw s!"{name}: parameter address requires 32 or 64 bits"
      else throw s!"unknown symbol {name}"
  | o => throw s!"unsupported source operand {repr o}"

/-- `[r]` or `[r+imm]` with a register of the given width. -/
def address (env : Env) (width : Nat) : Operand → M (Nat × Int)
  | .address [.register r] => return (← reg env width (.register r), 0)
  | .address [.offset "+" (.register r) (.literal t)] => do
    let .imm v ← literal t | throw s!"bad offset {t}"
    return (← reg env width (.register r), v)
  | o => throw s!"unsupported address {repr o}"

/-- Registers `{r0, ...}` of one width. -/
def regs (env : Env) (width : Nat) : List Operand → M (List Nat)
  | [] => pure []
  | o :: os => return (← reg env width o) :: (← regs env width os)

/-- A destination vector `{d0, ...}`: its registers must be distinct (§6.4.3: otherwise the
behaviour is undefined). Every instruction with a destination list decodes it here. -/
def dstRegs (env : Env) (width : Nat) (os : List Operand) : M (List Nat) := do
  let ds ← regs env width os
  unless ds.Nodup do throw "repeated register in a destination vector"
  pure ds

def srcs (env : Env) (width : Nat) : List Operand → M (List Opnd)
  | [] => pure []
  | o :: os => return (← src env width o) :: (← srcs env width os)

/-- A source operand of a floating instruction type: an integer constant is invalid at a
floating-point type (§9.4 Table 26). -/
def floatSrc (env : Env) (width : Nat) (o : Operand) : M Opnd := do
  let x ← src env width o
  match x with
  | .imm _ => throw "integer constant operand of a floating-point type"
  | _ => pure x

/-- Source operands of a floating instruction type (`floatSrc`). -/
def floatSrcs (env : Env) (width : Nat) : List Operand → M (List Opnd)
  | [] => pure []
  | o :: os => return (← floatSrc env width o) :: (← floatSrcs env width os)

/-- The data type a type token names. -/
def dtypeOf? : Isa.Token → Option DType
  | .pred => some .pred
  | .b1 => some (.int .b 1) | .b2 => some (.int .b 2) | .b4 => some (.int .b 4)
  | .b8 => some (.int .b 8) | .b16 => some (.int .b 16) | .b32 => some (.int .b 32)
  | .b64 => some (.int .b 64) | .b128 => some (.int .b 128)
  | .u2 => some (.int .u 2) | .u4 => some (.int .u 4) | .u8 => some (.int .u 8)
  | .u16 => some (.int .u 16) | .u32 => some (.int .u 32) | .u64 => some (.int .u 64)
  | .s2 => some (.int .s 2) | .s4 => some (.int .s 4) | .s8 => some (.int .s 8)
  | .s16 => some (.int .s 16) | .s32 => some (.int .s 32) | .s64 => some (.int .s 64)
  | .f16 => some (.float .f16) | .bf16 => some (.float .bf16) | .tf32 => some (.float .tf32)
  | .f32 => some (.float .f32) | .f64 => some (.float .f64)
  | .e4m3 => some (.float .e4m3) | .e5m2 => some (.float .e5m2)
  | .f16x2 => some (.packed (.float .f16) 2) | .bf16x2 => some (.packed (.float .bf16) 2)
  | .f32x2 => some (.packed (.float .f32) 2)
  | .e4m3x2 => some (.packed (.float .e4m3) 2) | .e5m2x2 => some (.packed (.float .e5m2) 2)
  | .e4m3x4 => some (.packed (.float .e4m3) 4) | .e5m2x4 => some (.packed (.float .e5m2) 4)
  | .e2m1x2 => some (.packed (.float .e2m1) 2) | .e2m1x4 => some (.packed (.float .e2m1) 4)
  | .e2m3x2 => some (.packed (.float .e2m3) 2) | .e2m3x4 => some (.packed (.float .e2m3) 4)
  | .e3m2x2 => some (.packed (.float .e3m2) 2) | .e3m2x4 => some (.packed (.float .e3m2) 4)
  | .ue8m0x2 => some (.packed (.float .ue8m0) 2) | .ue5m3x2 => some (.packed (.float .ue5m3) 2)
  | .s2f6x2 => some (.packed (.float .s2f6) 2)
  | .u16x2 => some (.packed (.int .u 16) 2) | .s16x2 => some (.packed (.int .s 16) 2)
  | .u8x4 => some (.packed (.int .u 8) 4) | .s8x4 => some (.packed (.int .s 8) 4)
  | _ => none

/-- The data type of a type token, or an error. -/
def dtype (t : Option Isa.Token) : M DType :=
  match t.bind dtypeOf? with
  | some d => pure d
  | none => throw "unsupported type token"

/-- The register widths a register of a data type has: the type's width, at least 16 bits for a
narrower floating or packed type. -/
def DType.regWidth (d : DType) : Nat :=
  match d with
  | .int _ w => w
  | .pred => 1
  | d => max 16 d.width

/-- The flag of an optional qualifier. -/
def flag (r : Isa.Raw) (s : Isa.Slot) : Bool := (r.get s).isSome

/-- The operand of a recognized instruction with the given name. -/
def opnd? (r : Isa.Raw) (name : String) : Option Isa.ROpnd :=
  r.opnds.find? (·.name == name)

/-- The operand as written of a recognized instruction with the given name. -/
def arg (r : Isa.Raw) (name : String) : M Operand :=
  match opnd? r name with
  | some o => pure o.op
  | none => throw s!"missing operand {name}"

/-- The operands as written of a recognized instruction with the given name, in order (a register
group is one operand per member). -/
def args (r : Isa.Raw) (name : String) : M (List Operand) :=
  match opnd? r name with
  | some o => match o.op with
    | .vector cs => pure cs
    | x => pure [x]
  | none => throw s!"missing operand {name}"

/-- The data type of an operand of a recognized instruction. -/
def ROpnd.dtype (o : Isa.ROpnd) : M DType :=
  match o.dtype.bind dtypeOf? with
  | some d => pure d
  | none => throw s!"operand {o.name} has no type"

/-- A source register or value of an operand's type: a predicate register, `.pred` special
register or integer constant for `.pred`, a floating source (no integer constant, Table 26) for a
floating or packed floating type, otherwise any source of the type's width. -/
def typedOpnd (env : Env) (d : DType) (o : Operand) : M Opnd :=
  match d with
  | .pred => match o with
    | .register r => match SReg.ofName? r with
      | some s => if s.width = 1 then pure (.sreg s) else throw s!"{r} is not a predicate"
      | none => .reg <$> reg env 1 o
    | .literal t => do
      match ← literal t with
      | .imm v => pure (.imm v)
      | _ => throw s!"{t} is not a predicate constant"
    | _ => .reg <$> reg env 1 o
  | .float _ | .packed (.float _) _ => floatSrc env d.width o
  | d => src env d.width o

/-- The source operands of a recognized operand: one per member of a register group. -/
def rsrcs (env : Env) (o : Isa.ROpnd) : M (List Opnd) := do
  let d ← ROpnd.dtype o
  match o.op with
  | .vector cs => cs.mapM (typedOpnd env d)
  | x => return [← typedOpnd env d x]

/-- The source operand of a recognized scalar operand. -/
def rsrc (env : Env) (o : Isa.ROpnd) : M Opnd := do
  typedOpnd env (← ROpnd.dtype o) o.op

/-- A destination register of a type's width, or `none` for the sink `_`. -/
def typedDst (env : Env) (d : DType) : Operand → M (Option Nat)
  | .sink => pure none
  | o => some <$> reg env d.width o

/-- The destination registers of a recognized operand, one per member of a register group; the
named registers of a group are distinct (§6.4.3). -/
def rdsts (env : Env) (o : Isa.ROpnd) : M (List (Option Nat)) := do
  let d ← ROpnd.dtype o
  let ds ← match o.op with
    | .vector cs => cs.mapM (typedDst env d)
    | x => return [← typedDst env d x]
  unless (ds.filterMap id).Nodup do throw "repeated register in a destination vector"
  pure ds

/-- The sources and destinations of a recognized instruction, in operand order: written operands
are destinations, the others sources. -/
def operands (env : Env) (r : Isa.Raw) : M (List (Option Nat) × List Opnd) :=
  r.opnds.foldlM (fun (ds, ss) o => do
    match o.role with
    | .w => return (ds ++ (← rdsts env o), ss)
    | _ => return (ds, ss ++ (← rsrcs env o))) ([], [])

end Decode

end PTX
