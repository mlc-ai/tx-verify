-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Syntax
public import Core.Source.DecodeOps

@[expose] public section

/-!
Decoder from source syntax to `PTX.Kernel`.

All string processing is structural recursion over `List Char`, so that decoding a
concrete kernel reduces in the Lean kernel (`decide`/`rfl`) without native code.
Unsupported or ill-typed forms are errors; nothing is silently dropped.
-/

/-! ## PROG-DECODE — from source to instructions
Statement: The decoder turns the parsed source of a kernel into the typed program that the model
  executes. The grammar recognizes each instruction as an instruction entry, and the layer of the
  entry's family builds the instruction's representation; headers, parameters, the shared, local
  and constant variable layouts, labels, branch tables and register numbering are decoded here. An
  instruction the grammar does not recognize or its family layer rejects fails decoding, so no code
  is dropped silently. A module decodes only for a single `.target` of `sm_70` or later.

Review: each kernel's module passes the target check in `Tests/Source/Target.lean`.

Defs: *

Source:
- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "Integer constants are 64-bits in
    size and are either signed or unsigned, i.e., every integer constant has type .s64 or .u64"
- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "Integer literals may be followed
    immediately by the letter U to indicate that the literal is unsigned."
- §4.5.1 (integer constants: hexadecimal, octal, binary, decimal): "literals are signed ( .s64 )
    unless the value cannot be fully represented in .s64 or the unsigned suffix is specified, in
    which case the literal is unsigned ( .u64 )"
- §4.5.5: "Unary plus and minus preserve the type of the input operand."
- §4.5.5: "-1U , -0xfabc123400000000 are unsigned."
- §4.5.2 (0f binary32 constants)
- §9.4 Table 26 (an `.sX`/`.uX` operand of an `.fX` instruction type is): "invalid"
- §6.4.3: "when specified as destination operand, all elements in vector expression must be unique,
    otherwise behavior is undefined"
- §9.7.14.1: "any variable declared within a scope is not available outside the scope"
- §9.7 (instruction syntax, modifiers and `.type` lists)
- §5.1.7 (shared variables)
- §11 (`.target`)
- §9.7.15.1
- §9.7.15.2
- §9.7.10.6 (sm_6x notes)
- §9.3: "predicate registers can be declared as .reg .pred p, q, r;"
- §5.1.6.1 (kernel parameters)
- §5.1.6.4: "ld.param.s32 %y, [buffer+8];"
- §6.4.1: "[var+immOff] a sum of address of addressable variable var containing a byte address plus
    a constant integer byte offset (signed, 32-bit)."
- §6.4.1: "The address must be naturally aligned to a multiple of the access size. If an address is
    not properly aligned, the resulting behavior is undefined."
- §5.4.5: "The variable will be aligned to an address which is an integer multiple of byte-count."
- §9.7.10.8 (ld `.vec` restrictions)
- §9.4.1 Table 28 (wider destination registers)
- §9.7.1.3 (mul): ".mode = { .hi, .lo, .wide };"
- §9.7.1.3 (mul): "The .wide suffix is supported only for 16- and 32-bit integer types."
- §9.7.1.13
- §9.7.1.14 (min, max): "min{.relu}.type2 d, a, b;"
- §9.7.9.1–§9.7.9.4 (and, or, xor, not): ".type = { .pred, .b16, .b32, .b64 };"
- §9.7.9.1–§9.7.9.4 (and, or, xor, not): "Allowed types include predicate registers."
- §9.7.9.9 (shr): ".type = { .b16, .b32, .b64, .u16, .u32, .u64, .s16, .s32, .s64 };"
- §9.7.3.3
- §9.7.3.4: "sub{.rnd}{.ftz}.f32x2 d, a, b;"
- §9.7.3.4: "The default value of rounding modifier is .rn ."
- §9.7.3.6: "fma.rnd{.ftz}.f32x2 d, a, b, c;"
- §9.7.3.6: "Rounding modifiers (no default):"
- §9.7.3.11
- §9.7.3.12: "max{.ftz}{.NaN}{.abs}.f32 d, a, b, c;"
- §9.7.3.13: "rcp.approx{.ftz}.f32 d, a;"
- §9.7.3.21: "ex2.approx{.ftz}.f32 d, a;"
- §9.7.7.2: "setp.CmpOp{.ftz}.type p[|q], a, b;"
- §9.3.1.2 (Tables 23 and 24)
- §9.7.10.28.5.3 (cp.async.bulk.tensor syntax)
- §9.7.18.10.10.1 (tcgen05.mma syntax)
- §9.7.18.8.3 and §9.7.18.8.4 (tcgen05.ld and tcgen05.st syntax, Tables 59 and 61)
- §4.5.3: "In PTX, integer constants may be used as predicates."
- §11.8.3: "Declare the maximum number of thread blocks (CTAs) allowed to be part of the cluster."
- §11.8.3: "Product of the number of CTAs in each cluster dimension specified in any invocation of
    the kernel is required to be less or equal to that specified in this directive. Otherwise
    invocation will result in a runtime error or kernel launch failure."

Direction: stricter

Effect: The decoder works in two layers: `Isa.Grammar.parse` recognizes it as one instruction entry
  with its modifier values and operands (PROG-ISA-GRAMMAR), and the layer of the entry's family
  (`Entry.family`) builds the `Op`: `IntInstr.ofRaw` (PROG-ISA-INT), `MoveInstr.ofRaw`
  (PROG-ISA-MOVE), `CvtInstr.ofRaw` (PROG-ISA-CVT), `MemAccess.ofRaw` and `AddrInstr.ofRaw`
  (PROG-ISA-MEM), `WarpInstr.ofRaw` (PROG-ISA-WARP), `MatrixInstr.ofRaw` (PROG-ISA-MATRIX),
  `FloatInstr.ofRaw` (PROG-ISA-FLOAT), `ctlOp` for control flow, and `keptOp` for the barrier,
  mbarrier, fence, copy, cluster launch control, `setmaxnreg` and `tcgen05` forms
  (PROG-ISA-SYNC-FORMS). An entry of the `multimem`, `texture` or `unmodeled` family, and an
  instruction a family layer has no representation for, decodes to `Op.unmodeled`, which has no
  rule. Each kernel's `decode_eq` checks, by evaluation, that its source decodes to the kernel its
  theorem is about, so a decoding error changes which program is proved, never the proof. Registers
  are numbered once, here: a register's id is its position in the kernel's declared-register order
  (declarations in statement order, scoped ones after hygienic renaming; `pre<n>` declares `pre0` …
  `pre(n-1)`), and `Kernel.regNames` lists the names by id. Control flow is decoded as follows.
  `bra{.uni}` takes a label of the function; `brx.idx{.uni}` takes a `.branchtargets` table, a label
  followed by the directive, declared before the instruction (§9.7.14.4: "The .branchtargets
  directive must be defined in the local function scope before it is used."), whose targets are
  labels of the function; a table label is not a branch target. `ret.uni` is not decoded. `.loc`
  source-location directives (§11.6.4) are checked and dropped. The target check is stricter. A
  module decodes only for `.target sm_70` or later (`target`, `module`). For `.target sm_6x or
  below` the ISA gives `barrier{.cta}` without `.aligned`, `bar.warp.sync` and `shfl.sync`
  convergence requirements (§9.7.15.1: "For .target sm_6x or below, barrier{.cta} instruction
  without .aligned modifier is equivalent to .aligned variant and has the same restrictions as of
  .aligned variant."; §9.7.15.2 and §9.7.10.6 likewise) that the model's sm_70 rules do not check,
  so such modules are rejected. A module without exactly one `.target` directive is rejected too
  (§11.1.2: "A .target directive specifies a single target architecture, but subsequent .target
  directives can be used to change the set of target features allowed during parsing"; a module with
  several is rejected rather than checking each). The directive names exactly one architecture,
  spelled `sm_n[a|f]` as in the §11.1.2 list or as its synonym `compute_n` ("Targets of the form
  compute_xx are also accepted as synonyms for sm_xx targets."), with the same sm_70 floor, and
  otherwise only the options `texmode_unified`, `texmode_independent` and `debug`; other spellings
  (`sm_70junk`), two architectures and unknown options are rejected. The option `map_f64_to_f32` is
  rejected too: it changes the meaning of every double-precision instruction (§11.1.2:
  "map_f64_to_f32 indicates that all double-precision instructions map to single-precision
  regardless of the target architecture."), and the model executes `.f64` instructions in double
  precision. Each kernel's
  module passes this check; its `decode_eq` decodes the kernel's function. Parameters are decoded as
  follows. A scalar kernel parameter is `.param .t name` or a pointer `.param .t .ptr [.space]
  [.align N] name` (§5.1.6.3, `.space` one of `.const`, `.global`, `.local`, `.shared`, N an integer
  literal (§4.5.1, `U` suffix allowed) that is a power of two, 4 when not written, `.t` 32 or 64
  bits); `name` may be a parameterized name `p<n>` declaring `p0` … `p(n-1)` (§5.4.6: "This
  shorthand syntax may be used with any of the fundamental types and with any state space"); any
  other attribute token is rejected. A scalar parameter with a storage alignment (`.param .align N
  .t name`, §5.4.5) is legal PTX that the decoder does not support, so it is rejected (stricter). A
  `.ptr` attribute with a state space or an alignment above 1 is kept in `Kernel.ptrParams`
  (alignment 1 with a generic address constrains nothing the launch check reads). A register
  declaration declares one name, a parameterized name `pre<n>` or a comma list of plain names (`.reg
  .t a, b, c`, §9.3), each a register of type `.t`, in source order; a list that mixes in a
  parameterized name is rejected (stricter). The directives `.maxntid` (1 to 3 extents, kept as
  their product, §11.5.2), `.reqntid` (1 to 3 extents, kept per dimension with an extent not written
  being 1: the directive declares a 1D, 2D or 3D CTA and §10.2 gives "%ntid.y == %ntid.z == 1 in 1D
  CTAs. %ntid.z ==1 in 2D CTAs."; not both, §11.5.3) are kept for CORRECT-LAUNCH; `.minperctamemory
  size` (§11.5.10, a 32-bit unsigned size) is kept in `Kernel.minPerCtaMemory`, and only a kernel
  with it may use `%perctamemoryoffset` and `%perctamemorysize` (§11.5.10: "Only entry functions
  specifying this directive are allowed to use special registers %perctamemoryoffset or
  %perctamemorysize ."; PROG-OPERAND). `.maxnreg`, `.minnctapersm` and `.maxclusterrank` are
  checked and dropped: the model represents no register counts (EXT-SETMAXNREG-EFFECTIVE), no
  residency, and the cluster's size comes from the launch (§11.8.3: "Product of the number of CTAs
  in each cluster dimension specified in any invocation of the kernel is required to be less or
  equal to that specified in this directive.").
  Parameter objects are decoded as follows. `ld.param{.v2,.v4}.t d, [obj]` or `[obj+off]` on a
  by-value parameter object `obj` (`.param .align N .t obj[n]`) reads `count` elements of `.t` from
  byte `off` of the object (THREAD-MOVE). It is rejected (stricter, `MemAccess.paramChecks`) when
  the access leaves the object (`off` negative or `off + size` beyond its bytes: the ISA gives such
  a read no meaning), when the access size does not divide both `off` and the declared alignment
  (then the address is aligned for no placement, or only for some placements, the declaration
  allows; a misaligned address is undefined), and for a `.vec`/`.type` pair `ld` admits only in the
  global space. A `.b128` element is read as two 64-bit halves (THREAD-MOVE). The destination
  registers have one width: the element width or a wider one (PROG-ISA-MEM); THREAD-MOVE applies to
  a wider destination of at most 64 bits of a bit-size `.t` only (Table 28 zero-extends every wider
  destination of a bit-size type). `ld.param` on a scalar parameter is `[p]` at the parameter's own
  width. Variables are decoded as follows. A kernel's `.shared .align A .b8 name[N]` and `.local
  .align A .b8 name[N]` variables and the module's `.shared` and `.const .align A .b8 name[N]`
  variables are laid out by the decoder (EXT-SHARED, EXT-LOCAL-CONST-LAYOUT); a `.const` variable
  with an initializer and every other `.local` or `.const` declaration form are rejected. Scopes and
  types are decoded as follows. Every name declared in a `{}` scope (register, label, `.shared` or
  `.local` variable) is bound in that scope only, under a hygienic name, so equal names in different
  scopes are different objects; names declared twice in one scope are errors. Each instruction
  accepts only the modifier combinations of its entry (PROG-ISA-GRAMMAR), and its registers must
  be declared at the widths of the operand types the family layer reads (PROG-OPERAND). The kept
  forms (`keptOp`) are described next. A form of those families that the description calls not
  decoded is recognized by the grammar and decodes to `Op.unmodeled` when the table has it. Tensor
  loads are decoded as follows. `.L2::cache_hint` stands after an optional `.multicast::cluster`,
  before or after `.cta_group` (§9.7.10.28.5.3 lists `{.cta_group}{.level::cache_hint}`; the text
  gives qualifier order no meaning, and ptxas accepts both), each qualifier at most once; its 64-bit
  `cache_policy` is the last operand, after `ctaMask`. Other qualifier orders are rejected (scope).
  The MMA operands are decoded as follows. `tcgen05.mma` takes its A operand as a shared descriptor
  or as a Tensor Memory address `[a-tmem]` or `[a-tmem+imm]` (THREAD-TC), the lane-mask vector or no
  mask (then `4 * group size` zero words, THREAD-TC), and `enable-input-d` as a predicate register
  or an integer constant (§4.5.3); a floating constant there is rejected. The destination `[d-tmem]`
  is a register. Tensor Memory loads and stores are decoded as follows. `tcgen05.ld` and
  `tcgen05.st` decode every `.shape1` and `.shape2` of §9.7.18.8.3 and §9.7.18.8.4 (`TcShape`), with
  `.num` from `.x1` to `.x128` and a vector of `num` repetitions of the shape's registers, an entry
  Tables 59 and 61 give (not NA). The address is `[taddr]` or `[taddr+0]`; `.16x32bx2` takes its
  `immHalfSplitoff` as a non-negative integer constant below `2 ^ 32`, after the address.
  `.pack::16b`, `.unpack::16b`, `.red`, `.spcompress` and a nonzero address offset are not decoded
  (scope). The rejected forms are as follows. Static undefined behaviour is rejected: a destination
  vector naming a register twice (every instruction with a destination list, PROG-OPERAND `rdsts`,
  `dstRegs`). Forms with no stated meaning are rejected too: an integer constant at a floating-point
  instruction type (Table 26), an integer constant wider than 64 bits (§4.5.1 gives constants 64
  bits and does not say how one is widened to 128), a scalar kernel parameter wider than 64 bits
  (the launch supplies a scalar parameter as 64 bits), and an integer literal whose value is not
  representable in `.u64` (§4.5.1: every integer constant is `.s64` or `.u64`, so no wider value is
  a constant). Other integer constant expressions (§4.5.4: unary plus, repeated unary operators,
  `!`, `~`, binary and ternary operators, parentheses, casts, `WARP_SZ`) are legal PTX that the
  decoder does not support, so they are rejected (stricter). Integer constants are decoded as
  follows. A constant is decoded with its §4.5.1 type: a literal is `.s64` unless its value is not
  representable in `.s64` or it has the `U` suffix, and then `.u64`; one unary minus applied to a
  literal keeps that type (§4.5.5), so it negates an `.s64` literal as an integer and a `.u64`
  literal modulo `2^64` (`-1U` is `2^64 - 1`, `-9223372036854775808` is the `.u64` value `2^63`).
  The operand holds the constant's value; data operands and address offsets use its 64-bit pattern,
  truncated to the width of the use (§4.5.1: "each integer constant is converted to the appropriate
  size based on the data or instruction type at its use").

### EXT-BRKPT — a reached breakpoint aborts the kernel

Statement: The model reads `brkpt` as `trap`: a thread that executes it performs an event of
  undefined behaviour, so no execution that reaches a breakpoint is accepted.

Why it is not spec text: The ISA says only that `brkpt` suspends execution. It does not say what a
  suspended thread does when no debugger is attached, whether it resumes, or what the other threads
  of the launch observe meanwhile. Compilers emit it behind a guarded branch for a failed debug
  assertion (CUTLASS `CUTLASS_ASSERT` under `nvcc` without `-DNDEBUG`), where reaching it means the
  program's own invariant is broken.

Evidence: PTX ISA §9.7.21.1 (brkpt): "Suspends execution" and §9.7.21.4 (trap): "Abort execution and
  generate an interrupt to the host CPU."

Direction: stricter

Effect: A kernel that contains `brkpt` can be proved only by showing that no consistent execution
  reaches one (`Correct.safe`). The decoded program holds `Op.trap` at the position of every
  `brkpt`; the instruction reads no register, so it does not affect DEP-CANONICAL-SPIN. Disclosed by
  every kernel whose statement names `Op.trap`: FlashMlaSparseDecodeH64.

### EXT-SHARED — shared memory layout

Statement: The model places each `.shared` variable at the decoder's offset from the shared base, in
  disjoint and aligned bytes of the CTA's shared memory. The PTX ISA does not say where variables
  are placed, so a kernel whose behaviour depends on the addresses beyond disjointness and alignment
  is outside the claim.

Why it is not spec text: Distinct `.shared` variables occupy disjoint, aligned bytes of the CTA's
  shared memory. The model places them at the decoder's offsets from `Launch.sharedBase`; a kernel
  whose behaviour depends on the actual addresses beyond disjointness and alignment is outside the
  claim. Obligations on the launch, not checked: `Launch.sharedBase` is aligned to the largest
  alignment of the kernel's shared variables, and an `extern` shared variable starts after the
  static ones at its own alignment.

Evidence: PTX ISA §5.1.7 ("Variables declared in .shared state space refer to the memory
  addresses in the current CTA") and §5.4.5 (alignment). Neither gives the placement of variables
  or the base address of the shared window, which the compiler and the driver choose.

Direction: reading

Effect: Disclosed by every kernel whose statement names `Opnd.sharedSym`: BlockSum, FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, TcGemm, TmaCopy.

### EXT-LOCAL-CONST-LAYOUT — local and constant variable layout

Statement: The model places each `.local` variable at the decoder's offset from the local base in
  every thread's local memory, and each `.const` variable at the decoder's offset from the constant
  base, in disjoint and aligned bytes. The PTX ISA does not say where variables are placed, so a
  kernel whose behaviour depends on the addresses beyond disjointness and alignment is outside the
  claim.

Source:
- §5.1.5: "The local state space ( .local ) is private memory for each thread to keep its own data."
- §5.1.3: "Statically-sized constant variables have an optional variable initializer; constant
    variables with no explicit initializer are initialized to zero by default."
- §5.4.5 (alignment)

Why it is not spec text: The text gives neither the placement of the variables nor the base
  addresses, which the compiler and the driver choose. A kernel's `.local .align A .b8 name[N]`
  variables are laid out in declaration order from `Launch.localBase` at their alignments, the same
  offsets in every thread's local memory, and the module's `.const .align A .b8 name[N]` variables
  in declaration order from `Launch.constBase` (`varLayout`). Obligations on the launch, not
  checked: each base is aligned to the largest alignment of its variables, and the bytes of the
  variables are allocated in `mem0`. The contents of a `.const` variable at launch are `mem0`'s
  bytes at its location (EXT-LAUNCH), which covers the zero default and a value the host wrote
  before the launch. A `.const` variable with an initializer is rejected at decoding: the model
  would need `mem0` to agree with the initializer, which the launch interface does not state.

Direction: reading

Effect: If it does not hold, a kernel that computes with the numeric address of a local or constant
  variable may reach other bytes than the model's. Disclosed by every kernel whose statement names
  `AddrBase.localSym`, `Opnd.localSym` or `AddrBase.constSym`: none.
-/

namespace PTX.Decode
open PTX.Syntax

/-- A control-flow instruction: `bra{.uni}` to a label, `brx.idx{.uni}` through a
`.branchtargets` table declared before it, `ret`, `exit`, `trap`, and `brkpt`, which decodes to
`trap` (EXT-BRKPT). `ret.uni` is not decoded. -/
def ctlOp (env : Env) (r : Isa.Raw) : M Op := do
  let uni := flag r .uni
  match r.entry with
  | .bra => do
    let .symbol l ← arg r "tgt" | throw "branch target"
    let some pc := env.labels.lookup l | throw s!"unresolved label {l}"
    return .bra pc uni
  | .brx_idx => do
    let index ← src env 32 (← arg r "index")
    let .symbol name ← arg r "tlist" | throw "branch table"
    let some (_, declared, targets) := env.tables.find? (·.1 == name)
      | throw s!"unresolved branch table {name}"
    unless declared ≤ env.pc do throw s!"branch table {name} is declared after its use"
    return .brx index targets uni
  | .ret => if uni then throw "ret.uni is not decoded" else pure .ret
  | .exit => pure .exit
  | .trap => pure .trap
  | .brkpt => pure .trap
  | _ => throw "not a control-flow instruction"

/-- Decode one instruction: the grammar recognizes it as an instruction entry (`Grammar.parse`),
and the layer of the entry's family builds the `Op`. -/
def op (env : Env) (opcode : String) (args : List Operand) : M Op := do
  let r ← Isa.Grammar.parse env.isPred opcode args
  match r.entry.family with
  | .int => .int <$> IntInstr.ofRaw env r
  | .float => .float <$> FloatInstr.ofRaw env r
  | .move => .move <$> MoveInstr.ofRaw env r
  | .cvt => .cvt <$> CvtInstr.ofRaw env r
  | .mem => match r.entry with
    | .cvta | .cvta_generic | .mapa | .mapa_generic | .isspacep | .getctarank
    | .getctarank_generic | .prefetch | .prefetch_valid_addr | .prefetchu | .applypriority =>
      (fun c => match c with | some c => .addr c | none => .unmodeled r) <$> AddrInstr.ofRaw env r
    | _ => (fun a => match a with | some a => .mem a | none => .unmodeled r) <$>
      MemAccess.ofRaw env r
  | .warp => .warp <$> WarpInstr.ofRaw env r
  | .ctl => ctlOp env r
  | .matrix => (fun m => match m with | some m => .matrix m | none => .unmodeled r) <$>
    MatrixInstr.ofRaw env r
  | .multimem | .texture | .unmodeled => pure (.unmodeled r)
  | .barrier | .fence | .mbarrier | .async | .tc | .clc | .misc => keptOp env r

/-- A lexical binding. A register range `pre<count>` binds `pre0` … `pre(count-1)`;
`count = 0` binds the single name `pre` (a scalar register or a label). -/
structure Binding where
  pre : List Char
  count : Nat
  target : String
  isReg : Bool

/-- The resolved name of `s` under `b`, if `b` binds it. -/
def Binding.lookup (b : Binding) (s : List Char) : Option String :=
  if b.count = 0 then (if b.pre = s then some b.target else none)
  else match stripPrefix b.pre s with
    | some rest => match canonIndex? rest with
      | some i => if i < b.count then some (b.target ++ String.ofList rest) else none
      | none => none
    | none => none

/-- The innermost binding of `s`. -/
def findBinding : List Binding → List Char → Option (String × Bool)
  | [], _ => none
  | b :: bs, s => match b.lookup s with
    | some t => some (t, b.isReg)
    | none => findBinding bs s

def boundName (env : List Binding) (s : String) : String :=
  ((findBinding env s.toList).map (·.1)).getD s

mutual
/-- Resolve all operand forms, including PTX registers without a `%` prefix. -/
def resolveOperand (env : List Binding) : Operand → Operand
  | .register r => .register (boundName env r)
  | .symbol s => match findBinding env s.toList with
    | some (t, true) => .register t
    | some (t, false) => .symbol t
    | none => .symbol s
  | .address xs => .address (resolveOperands env xs)
  | .vector xs => .vector (resolveOperands env xs)
  | .offset sign x y => .offset sign (resolveOperand env x) (resolveOperand env y)
  | .negate x => .negate (resolveOperand env x)
  | .pair xs => .pair (resolveOperands env xs)
  | o => o

def resolveOperands (env : List Binding) : List Operand → List Operand
  | [] => []
  | x :: xs => resolveOperand env x :: resolveOperands env xs
end

/-- Whether two declarations (`pre`, `count` as in `Binding`) declare a common name.
For two ranges, `pa ++ i = pb ++ j` has a solution iff it has one with `i = 0` or `j = 0`,
since a longer prefix consumes leading digits of the other index. -/
def declOverlap (a b : List Char × Nat) : Bool :=
  let names := fun (p : List Char) (c : Nat) (n : List Char) => (
    if c = 0 then decide (p = n) else match stripPrefix p n with
      | some rest => match canonIndex? rest with | some i => decide (i < c) | none => false
      | none => false : Bool)
  match a.2, b.2 with
  | 0, _ => names b.1 b.2 a.1
  | _, 0 => names a.1 a.2 b.1
  | ca, cb => decide (a.1 = b.1) || names a.1 ca (b.1 ++ ['0']) || names b.1 cb (a.1 ++ ['0'])

def declsDisjoint : List (List Char × Nat) → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !declOverlap x y) && declsDisjoint xs

/-- The name a `.local` variable declaration declares (`varLayout`'s form). -/
def localName? : List String → Option String
  | [".local", ".align", _, ".b8", name, "[", _, "]"] => some name
  | _ => none

/-- The name a `.shared` variable declaration declares (`sharedLayout`'s forms). -/
def sharedName? : List String → Option String
  | [".shared", ".align", _, ".b8", name, "[", _, "]"] => some name
  | [".extern", ".shared", ".align", _, ".b8", name, "[", "]"] => some name
  | _ => none

/-- Keep top-level names and qualify names within a nested scope. -/
def qualifyScopeName (path name : String) : String :=
  if path = "" then name else "#" ++ path ++ "#" ++ name

/-- The bindings of one lexical scope, shared by all its statements. -/
def scopeBindings (body : List Statement) (outer : List Binding) (path : String) :
    M (List Binding) := do
  let regs ← body.filterMap (fun s => match s with
    | .declaration ts => if ts.head? = some ".reg" then some ts else none
    | _ => none) |>.flatMapM regClass
  let labels := body.filterMap fun s => match s with | .label l => some l | _ => none
  let shared := body.filterMap fun s => match s with
    | .declaration ts =>
      if ts.head? = some ".shared" then sharedName? ts
      else if ts.head? = some ".local" then localName? ts else none
    | _ => none
  unless declsDisjoint (regs.map (fun c => (c.pre, c.count)) ++
      (labels ++ shared).map (fun l => (l.toList, 0))) do
    throw "duplicate declaration in one lexical scope"
  let regBinding (c : RegClass) :=
    Binding.mk c.pre c.count (qualifyScopeName path (String.ofList c.pre)) true
  return regs.map regBinding ++
    (labels ++ shared).map (fun l => Binding.mk l.toList 0 (qualifyScopeName path l) false) ++ outer

/-- Resolve one statement using its index in the enclosing scope. -/
def resolveScopeStmt
    (resolveNested : List Statement → List Binding → String → M (List Statement))
    (env : List Binding) (path : String) (item : Statement × Nat) : M (List Statement) :=
  let qualify := qualifyScopeName path
  let (s, i) := item
  match s with
  | .scope sub => resolveNested sub env (path ++ "/" ++ toString i)
  | .instruction p op args => pure [.instruction
      (p.map fun (r, n) => (boundName env r, n)) op (args.map (resolveOperand env))]
  | .label l => pure [.label (boundName env l)]
  | .directive (".branchtargets" :: targets) =>
      pure [.directive (".branchtargets" :: targets.map fun l =>
        if l = "," then l else boundName env l)]
  | .declaration [".reg", ty, name] =>
      pure [.declaration [".reg", ty, qualify name]]
  | .declaration [".reg", ty, pre, "<", n, ">"] =>
      pure [.declaration [".reg", ty, qualify pre, "<", n, ">"]]
  | .declaration (".reg" :: ty :: names@(_ :: "," :: _)) =>
      pure [.declaration (".reg" :: ty :: names.map fun n => if n = "," then n else qualify n)]
  | .declaration [".shared", ".align", a, ".b8", name, "[", n, "]"] =>
      pure [.declaration [".shared", ".align", a, ".b8", qualify name, "[", n, "]"]]
  | .declaration [".local", ".align", a, ".b8", name, "[", n, "]"] =>
      pure [.declaration [".local", ".align", a, ".b8", qualify name, "[", n, "]"]]
  | other => pure [other]

/-- Resolve statements using the bindings of their enclosing scope and their original indices. -/
def resolveScopePart
    (resolveNested : List Statement → List Binding → String → M (List Statement))
    (body : List Statement) (env : List Binding) (path : String) (start : Nat) :
    M (List Statement) :=
  List.flatten <$> (body.zipIdx start).mapM (resolveScopeStmt resolveNested env path)

/-- Hygienic lexical resolution. Fuel is supplied by the size of the input syntax;
there is no fixed nesting limit. Generated names contain `#`, which PTX identifiers
cannot contain, so they cannot collide with source-level names. -/
def resolveScopes : Nat → List Statement → List Binding → String → M (List Statement)
  | 0, _, _, _ => throw "scope traversal exhausted input size"
  | fuel + 1, body, outer, path => do
    let env ← scopeBindings body outer path
    resolveScopePart (resolveScopes fuel) body env path 0

mutual
/-- Structural nesting depth, used only to bound traversal of the finite AST. -/
def statementDepth : Statement → Nat
  | .scope body => scopeDepth body + 1
  | _ => 1

def scopeDepth : List Statement → Nat
  | [] => 1
  | s :: ss => max (statementDepth s) (scopeDepth ss)
end

/-- Nonempty decimal source-location fields. -/
def locNumber (s : String) : Bool := match s.toList with
  | [] => false
  | cs => (digits 10 digit? cs 0).isSome

/-- Source-location metadata (§11.6.4) has no execution effect. The supported syntax includes
the optional `function_name` and `inlined_at` attributes, with an optional positive offset. -/
def locDirective : List String → Bool
  | [".loc", f, l, c] => [f, l, c].all locNumber
  | [".loc", f, l, c, ",", "function_name", name, ",", "inlined_at", f', l', c'] =>
      name.toList != [] && [f, l, c, f', l', c'].all locNumber
  | [".loc", f, l, c, ",", "function_name", name, "+", off, ",", "inlined_at", f', l', c'] =>
      name.toList != [] && [f, l, c, off, f', l', c'].all locNumber
  | _ => false

/-- Explicit target-label lists of `.branchtargets` (§11.4.1). -/
def branchTargetNames : List String → M (List String)
  | [name] => if name = "," then throw "empty branch target" else pure [name]
  | name :: "," :: rest => do
      if name = "," then throw "empty branch target"
      return name :: (← branchTargetNames rest)
  | _ => throw "expected nonempty comma-separated branch target labels"

/-- The labelled branch tables with the index of the next instruction, in declaration order. The
table is the directive that immediately follows its label. -/
def branchTableDecls : List Statement → Nat → M (List (String × Nat × List String))
  | [], _ => pure []
  | .label name :: .directive (".branchtargets" :: ts) :: rest, pc => do
      let targets ← branchTargetNames ts
      return (name, pc, targets) :: (← branchTableDecls rest pc)
  | .directive (".branchtargets" :: _) :: _, _ => throw "branch table has no label"
  | .instruction .. :: rest, pc => branchTableDecls rest (pc + 1)
  | _ :: rest, pc => branchTableDecls rest pc

/-- Resolve every target of a table to an instruction label of the function (§9.7.14.4: "It must
refer to labels within the current function."). -/
def resolveBranchTables (labels : List (String × Nat))
    (decls : List (String × Nat × List String)) : M (List (String × Nat × List Nat)) :=
  decls.mapM fun (name, pc, targets) => do
    let pcs ← targets.mapM fun target => do
      let some n := labels.lookup target | throw s!"unresolved branch target {target}"
      pure n
    pure (name, pc, pcs)

/-- Flatten scopes: (declarations, labels with instruction index, instructions). -/
def flatten : List Statement → Nat →
    M (List (List String) × List (String × Nat) ×
      List (Option (String × Bool) × String × List Operand))
  | [], _ => pure ([], [], [])
  | s :: rest, n => do
    match s with
    | .instruction p o a =>
      let (d, l, i) ← flatten rest (n + 1)
      pure (d, l, (p, o, a) :: i)
    | .label name =>
      let (d, l, i) ← flatten rest n
      pure (d, (name, n) :: l, i)
    | .declaration ts =>
      let (d, l, i) ← flatten rest n
      pure (ts :: d, l, i)
    | .directive [".pragma", "\"nounroll\""] => flatten rest n
    | .directive (".branchtargets" :: _) => flatten rest n
    | .directive ts =>
      if locDirective ts then flatten rest n else throw s!"unsupported directive {ts}"
    | .scope _ => throw "nested scopes are not supported yet"

def splitTokens (sep : String) : List String → List String → List (List String)
  | [], acc => [acc.reverse]
  | t :: ts, acc =>
    if t = sep then acc.reverse :: splitTokens sep ts [] else splitTokens sep ts (t :: acc)

/-- The words of a dotted attribute token (`.ptr.global.align` gives `ptr`, `global`, `align`;
§5.1.6.3: "Spaces between .ptr , .space , and .align may be eliminated"). -/
def dotWords : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc => if c = '.' then acc.reverse :: dotWords cs [] else dotWords cs (c :: acc)

/-- The attribute tokens of a scalar parameter: dotted words on the left, other tokens on the
right. -/
def attrWords (ts : List String) : List (List Char ⊕ List Char) :=
  ts.flatMap fun t => match t.toList with
    | '.' :: cs => (dotWords cs []).map .inl
    | cs => [.inr cs]

def ptrSpace? : List Char → Option PtrSpace
  | ['c', 'o', 'n', 's', 't'] => some .const
  | ['g', 'l', 'o', 'b', 'a', 'l'] => some .global
  | ['l', 'o', 'c', 'a', 'l'] => some .local
  | ['s', 'h', 'a', 'r', 'e', 'd'] => some .shared
  | _ => none

/-- An alignment `N` of `.align N` (§5.4.5): an integer literal (§4.5.1, `intLit`) that is a
power of two. -/
def alignment (what n : String) : M Nat := do
  let (a, _) ← intLit n n.toList
  unless 0 < a ∧ a &&& (a - 1) = 0 do throw s!"{what} alignment is not a power of two"
  pure a

/-- `.ptr [.space] [.align N]` (§5.1.6.3): N a power of two, 4 when not written. -/
def ptrDecl : List (List Char ⊕ List Char) → M PtrDecl
  | .inl ['p', 't', 'r'] :: rest => do
    let (space, rest) := match rest with
      | .inl s :: r => match ptrSpace? s with
        | some sp => (some sp, r)
        | none => (none, rest)
      | _ => (none, rest)
    match rest with
    | [] => pure ⟨space, 4⟩
    | [.inl ['a', 'l', 'i', 'g', 'n'], .inr n] =>
      return ⟨space, ← alignment "pointer" (String.ofList n)⟩
    | _ => throw "unsupported pointer attribute"
  | _ => throw "unsupported parameter attribute"

/-- One parameter declaration: `.param .<t> [.ptr [.space] [.align N]] name`, where `name` may be
the parameterized `pre<n>` declaring `pre0` … `pre(n-1)` (§5.4.6, `RegClass.names`). -/
def param : List String → M (List (String × Nat) × Option PtrDecl)
  | ".param" :: ty :: rest => do
    let some w := typeWidth (String.ofList (ty.toList.drop 1)) | throw s!"parameter type {ty}"
    let (names, attrToks) ← match rest.reverse with
      | ">" :: n :: "<" :: pre :: r => do
        let some c := natLit? n.toList | throw s!"parameter count {n}"
        unless 0 < c do throw s!"parameter declaration {pre}"
        pure ((RegClass.mk pre.toList c w).names, r.reverse)
      | name :: r => pure ([name], r.reverse)
      | [] => throw "missing parameter name"
    let ps := names.map (·, w)
    let attrs := attrWords attrToks
    if attrs.isEmpty then pure (ps, none)
    else
      unless w = 32 ∨ w = 64 do throw s!"pointer parameter type {ty}"
      pure (ps, some (← ptrDecl attrs))
  | ts => throw s!"unsupported parameter {ts}"

/-- Fixed-size by-value arrays in the kernel parameter space. They are not scalar
pointer parameters. Keep the declared storage extent and alignment (ISA §5.1.6.1,
§5.4.2, §5.4.5); address and contents are supplied separately by the launch model. -/
def paramObjectOf (ty name n : String) (align : Option String) : M ParamObjectDecl := do
  let some w := typeWidth (String.ofList (ty.toList.drop 1)) | throw s!"parameter type {ty}"
  let some count := natLit? n.toList | throw s!"parameter array extent {n}"
  let al ← match align with
    | none => pure (w / 8)
    | some a => alignment "parameter" a
  unless ty.toList.head? = some '.' ∧ 0 < w ∧ w % 8 = 0 do
    throw s!"invalid parameter element type {ty}"
  unless 0 < count do throw "zero parameter array extent"
  pure ⟨name, w, count, al⟩

def paramObject : List String → M ParamObjectDecl
  | [".param", ".align", a, ty, name, "[", n, "]"] => paramObjectOf ty name n (some a)
  | [".param", ty, name, "[", n, "]"] => paramObjectOf ty name n none
  | ts => throw s!"unsupported parameter object {ts}"

/-- Separate scalar values from addressable array objects: a by-value tensor map is not a
64-bit pointer value. A `.ptr` attribute is kept when it constrains
a launch: a state space or an alignment above 1. -/
def parameterDecls (header : List String) :
    M (List (String × Nat) × List (String × PtrDecl) × List ParamObjectDecl) := do
  let rest := header.dropWhile (· ≠ "(")
  let "(" :: rest := rest | throw "kernel without parameter list"
  let inner := rest.takeWhile (· ≠ ")")
  unless inner.length < rest.length do throw "unterminated parameter list"
  let parts := if inner.isEmpty then [] else splitTokens "," inner []
  parts.foldlM (fun (scalars, ptrs, objects) ts => do
    if ts.contains "[" then
      return (scalars, ptrs, objects ++ [← paramObject ts])
    else
      let (ps, d) ← param ts
      let ptrs := match d with
        | some d => if d.space.isSome ∨ 1 < d.align then ptrs ++ ps.map (·.1, d) else ptrs
        | none => ptrs
      return (scalars ++ ps, ptrs, objects)) ([], [], [])

/-- The launch-shape directives of a kernel (§11.5): the `.maxntid` CTA size (the product of its
extents), the `.reqntid` CTA shape and the `.minperctamemory` size. -/
structure Directives where
  maxThreads : Option Nat := none
  reqThreads : Option (Nat × Nat × Nat) := none
  minPerCtaMemory : Option Nat := none
  deriving DecidableEq, Repr

/-- A positive literal of directive `d`. -/
def positive (d n : String) : M Nat :=
  match natLit? n.toList with
  | some v => if 0 < v then pure v else throw s!"zero {d}"
  | none => throw s!"{d} {n}"

/-- The thread count `nx [, ny [, nz]]` of `.maxntid`: the product of the extents. -/
def threads (d : String) (ns : List String) : M Nat :=
  ns.foldlM (fun p n => return p * (← positive d n)) 1

/-- The CTA shape `nx [, ny [, nz]]` of `.reqntid`; an extent not written is 1 (§10.2). -/
def shape (d : String) : List String → M (Nat × Nat × Nat)
  | [x] => return (← positive d x, 1, 1)
  | [x, y] => return (← positive d x, ← positive d y, 1)
  | [x, y, z] => return (← positive d x, ← positive d y, ← positive d z)
  | _ => throw s!"{d} extents"

/-- Decode the represented performance directives. `.maxntid` and `.reqntid` (not together,
§11.5.3) constrain the launch (CORRECT-LAUNCH). `.maxnreg` (§11.5.1), `.minnctapersm` (§11.5.4) and
`.maxclusterrank` (§11.8.3) are compiler/launch hints that no rule reads: the model represents no
register counts (EXT-SETMAXNREG-EFFECTIVE), no residency, and the cluster's size is the launch's;
the cluster-rank bound is a launch obligation, not an instruction rule. Check their syntax and drop
them; `dropped` lists the dropped directives already seen. -/
def headerTailAux (acc : Directives) (dropped : List String) : List String → M Directives
  | [] =>
    if acc.maxThreads.isSome ∧ acc.reqThreads.isSome then throw ".reqntid with .maxntid"
    else pure acc
  | ".maxntid" :: x :: "," :: y :: "," :: z :: rest => do
    unless acc.maxThreads.isNone do throw "duplicate .maxntid"
    headerTailAux { acc with maxThreads := some (← threads ".maxntid" [x, y, z]) } dropped rest
  | ".maxntid" :: x :: "," :: y :: rest => do
    unless acc.maxThreads.isNone do throw "duplicate .maxntid"
    headerTailAux { acc with maxThreads := some (← threads ".maxntid" [x, y]) } dropped rest
  | ".maxntid" :: x :: rest => do
    unless acc.maxThreads.isNone do throw "duplicate .maxntid"
    headerTailAux { acc with maxThreads := some (← threads ".maxntid" [x]) } dropped rest
  | ".reqntid" :: x :: "," :: y :: "," :: z :: rest => do
    unless acc.reqThreads.isNone do throw "duplicate .reqntid"
    headerTailAux { acc with reqThreads := some (← shape ".reqntid" [x, y, z]) } dropped rest
  | ".reqntid" :: x :: "," :: y :: rest => do
    unless acc.reqThreads.isNone do throw "duplicate .reqntid"
    headerTailAux { acc with reqThreads := some (← shape ".reqntid" [x, y]) } dropped rest
  | ".reqntid" :: x :: rest => do
    unless acc.reqThreads.isNone do throw "duplicate .reqntid"
    headerTailAux { acc with reqThreads := some (← shape ".reqntid" [x]) } dropped rest
  | ".minperctamemory" :: n :: rest => do
    unless acc.minPerCtaMemory.isNone do throw "duplicate .minperctamemory"
    let some v := natLit? n.toList | throw s!".minperctamemory {n}"
    unless v < 2 ^ 32 do throw s!".minperctamemory {n}"
    headerTailAux { acc with minPerCtaMemory := some v } dropped rest
  | ".maxnreg" :: n :: rest => do
    if ".maxnreg" ∈ dropped then throw "duplicate .maxnreg"
    let _ ← positive ".maxnreg" n
    headerTailAux acc (".maxnreg" :: dropped) rest
  | ".minnctapersm" :: n :: rest => do
    if ".minnctapersm" ∈ dropped then throw "duplicate .minnctapersm"
    let _ ← positive ".minnctapersm" n
    headerTailAux acc (".minnctapersm" :: dropped) rest
  | ".maxclusterrank" :: n :: rest => do
    if ".maxclusterrank" ∈ dropped then throw "duplicate .maxclusterrank"
    let _ ← positive ".maxclusterrank" n
    headerTailAux acc (".maxclusterrank" :: dropped) rest
  | ts => throw s!"unsupported kernel directives {ts}"

def headerTail (ts : List String) : M Directives := headerTailAux {} [] ts

def alignUp (n a : Nat) : Nat := (n + a - 1) / a * a

/-- `.shared .align A .b8 name[N]`, laid out in declaration order from `bytes`.
The real layout is chosen by ptxas; proofs may only rely on alignment and disjointness. -/
def sharedLayout : List (List String) → Nat → M (List (String × Nat) × Nat)
  | [], bytes => pure ([], bytes)
  | d :: ds, bytes => do
    match d with
    | [".shared", ".align", a, ".b8", name, "[", n, "]"] =>
      let some al := natLit? a.toList | throw s!"alignment {a}"
      let some size := natLit? n.toList | throw s!"size {n}"
      unless al > 0 do throw "zero alignment"
      let off := alignUp bytes al
      let (rest, total) ← sharedLayout ds (off + size)
      pure ((name, off) :: rest, total)
    | [".extern", ".shared", ".align", a, ".b8", name, "[", "]"] =>
      -- Dynamically sized: placed after the static variables; its size is the launch's.
      let some al := natLit? a.toList | throw s!"alignment {a}"
      unless al > 0 do throw "zero alignment"
      let off := alignUp bytes al
      let (rest, total) ← sharedLayout ds off
      pure ((name, off) :: rest, total)
    | ts => throw s!"unsupported shared declaration {ts}"

/-- `.local .align A .b8 name[N]` or `.const .align A .b8 name[N]` declarations of space `sp`,
laid out in declaration order from byte `bytes` at their alignments (EXT-LOCAL-CONST-LAYOUT).
Every other form is rejected, among them a `.const` declaration with an initializer. -/
def varLayout (sp : String) : List (List String) → Nat → M (List (String × Nat))
  | [], _ => pure []
  | d :: ds, bytes => do
    match d with
    | [s, ".align", a, ".b8", name, "[", n, "]"] =>
      unless s = sp do throw s!"unsupported {sp} declaration {d}"
      let some al := natLit? a.toList | throw s!"alignment {a}"
      let some size := natLit? n.toList | throw s!"size {n}"
      unless al > 0 do throw "zero alignment"
      let off := alignUp bytes al
      return (name, off) :: (← varLayout sp ds (off + size))
    | ts => throw s!"unsupported {sp} declaration {ts}"

def guard (env : Env) : Option (String × Bool) → M (Option (Nat × Bool))
  | none => pure none
  | some (p, n) => return some (← reg env 1 (.register p), n)

/-- Flat numbered register banks already have globally distinct register spellings. -/
def needsScopeResolution (body : List Statement) : Bool :=
  body.any fun s => match s with
    | .scope _ | .declaration [".reg", _, _] | .declaration (".reg" :: _ :: _ :: "," :: _) => true
    | _ => false

/-- The source form of one instruction: its guard and its opcode with operands. -/
abbrev SourceInstr := Option (String × Bool) × String × List Operand

/-- Everything `kernelIn` computes from the whole function before it decodes the instructions:
the decoding environment, the instructions in source order, and the kernel without code. -/
structure Prepared where
  env : Env
  instrs : List SourceInstr
  header : Kernel

/-- The declarations, labels, branch tables, shared layout and header after lexical resolution. -/
def prepareResolved (globals : List (List String)) (f : Function) (body : List Statement) :
    M Prepared := do
  let (decls, labels, instrs) ← flatten body 0
  let (sharedDecls, otherDecls) := decls.partition (fun d => d.head? = some ".shared")
  let (localDecls, regDecls) := otherDecls.partition (fun d => d.head? = some ".local")
  let classes ← regDecls.flatMapM regClass
  -- Static variables first, then module-scope `.extern .shared` arrays.
  -- Unreferenced `.global` objects do not occupy the CTA's shared window. Their
  -- symbols are not installed in Env: an instruction referencing one still fails
  -- decoding until global-symbol/address/initializer semantics are provided.
  let sharedGlobals :=
    globals.filter (fun d => d.head? != some ".global" && d.head? != some ".const")
  let locals ← varLayout ".local" localDecls 0
  let consts ← varLayout ".const" (globals.filter (fun d => d.head? == some ".const")) 0
  unless (locals.map (·.1)).Nodup ∧ (consts.map (·.1)).Nodup do
    throw "duplicate .local or .const variable"
  -- One `.shared` variable per name in each scope: the kernel's own (nested ones already
  -- renamed) and the module's; a kernel variable shadows a module one of the same name.
  unless (sharedDecls.filterMap sharedName?).Nodup ∧ (sharedGlobals.filterMap sharedName?).Nodup do
    throw "duplicate .shared variable"
  let (shared, bytes) ← sharedLayout (sharedDecls ++ sharedGlobals) 0
  let (ps, ptrParams, paramObjects) ← parameterDecls f.header
  let d ← headerTail ((f.header.dropWhile (· ≠ ")")).drop 1)
  let btabs ← branchTableDecls body 0
  let labels := labels.filter fun l => !(btabs.map (·.1)).contains l.1
  let tables ← resolveBranchTables labels btabs
  let env : Env :=
    { classes, labels, params := ps ++ paramObjects.map (fun p => (p.name, p.bytes * 8)), shared,
      objects := paramObjects, tables, locals, consts,
      perCtaMemory := d.minPerCtaMemory.isSome }
  let header : Kernel :=
    { name := f.name, params := ps, paramObjects, sharedBytes := bytes, ptrParams,
      maxThreads := d.maxThreads, reqThreads := d.reqThreads,
      minPerCtaMemory := d.minPerCtaMemory, regNames := classes.flatMap RegClass.names, code := [] }
  return { env, instrs, header }

/-- The decoding environment and instruction list before instruction decoding. -/
def prepare (globals : List (List String)) (f : Function) : M Prepared := do
  unless f.header.take 2 = [".visible", ".entry"] do throw "only .visible .entry kernels"
  let body ← if needsScopeResolution f.body then
      resolveScopes (scopeDepth f.body) f.body [] "" else pure f.body
  prepareResolved globals f body

/-- Decode the instructions `xs` against `env`, the first one at index `pc`, in order; the
first instruction that fails decoding fails the whole list. -/
def code (env : Env) (pc : Nat) (xs : List SourceInstr) : M (List Instr) :=
  (xs.zipIdx pc).mapM fun ((p, o, a), i) =>
    return { guard := ← guard env p, op := ← op { env with pc := i } o a }

/-- Decode kernel `f` of a module with module-scope declarations `globals`. -/
def kernelIn (globals : List (List String)) (f : Function) : M Kernel := do
  let p ← prepare globals f
  return { p.header with code := ← code p.env 0 p.instrs }

/-- Decode a kernel function that has no module-scope declarations. -/
def kernel (f : Function) : M Kernel := kernelIn [] f

/-- The architecture targets listed by the §11.1.2 syntax (with their `a`/`f` suffix forms). -/
def archTargets : List String :=
  ["sm_120a", "sm_120f", "sm_120", "sm_121a", "sm_121f", "sm_121", "sm_110a", "sm_110f", "sm_110",
   "sm_100a", "sm_100f", "sm_100", "sm_101a", "sm_101f", "sm_101", "sm_103a", "sm_103f", "sm_103",
   "sm_107a", "sm_107f", "sm_107", "sm_90a", "sm_90", "sm_80", "sm_86", "sm_87", "sm_88", "sm_89",
   "sm_70", "sm_72", "sm_75", "sm_60", "sm_61", "sm_62", "sm_50", "sm_52", "sm_53",
   "sm_30", "sm_32", "sm_35", "sm_37", "sm_20", "sm_10", "sm_11", "sm_12", "sm_13"]

/-- The platform options of the §11.1.2 syntax that leave the model's instruction semantics
unchanged; `map_f64_to_f32` changes the precision of the double-precision instructions and is not
one of them. -/
def targetOptions : List String :=
  ["texmode_unified", "texmode_independent", "debug"]

/-- The architecture number `n` of a target specifier `sm_n[a|f]`, or of its synonym
`compute_n[a|f]`; `none` for any other spelling. -/
def smNumber (t : String) : Option Nat :=
  let cs := t.toList
  let name := match cs with
    | 'c' :: 'o' :: 'm' :: 'p' :: 'u' :: 't' :: 'e' :: '_' :: rest => 's' :: 'm' :: '_' :: rest
    | _ => cs
  if archTargets.any (·.toList = name) then
    digits 10 digit? ((name.drop 3).takeWhile fun c => (digit? c).isSome) 0
  else none

/-- A `.target` string list: comma-separated specifiers, each an architecture or a platform
option. -/
def targetItems : List String → M (List String)
  | [] => throw "empty .target"
  | [t] => pure [t]
  | t :: "," :: rest => do return t :: (← targetItems rest)
  | ts => throw s!"malformed .target {ts}"

/-- The module's `.target` directive: exactly one directive, with exactly one architecture
specifier (`sm_n` or `compute_n`, spelled as in §11.1.2) of `sm_70` or later, plus only the
listed platform options. -/
def target (directives : List (List String)) : M Unit := do
  match directives.filter (·.head? = some ".target") with
  | [_ :: ts] =>
    let items ← targetItems ts
    let archs := items.filterMap smNumber
    unless items.all (fun t => (smNumber t).isSome ∨ targetOptions.contains t) do
      throw s!"unsupported .target {ts}: unknown specifier"
    let [n] := archs | throw s!"unsupported .target {ts}: needs exactly one architecture"
    unless 70 ≤ n do throw s!"unsupported .target {ts}: sm_6x or below"
  | _ => throw "a module needs exactly one .target directive"

/-- Decode kernel `f` of module `m`: the module's target, then the kernel. -/
def module (m : Module) (f : Function) : M Kernel := do
  target m.directives
  kernelIn m.globals f

end PTX.Decode
