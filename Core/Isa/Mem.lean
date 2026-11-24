-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Operand
public import Core.Isa.Rule

@[expose] public section

/-!
# Memory access and address instructions

Loads, stores, atomics and reductions (`MemAccess`), and the address conversions `cvta`, `mapa`,
`isspacep` and `getctarank` (`AddrInstr`).
-/

namespace PTX

/-! ## PROG-ISA-MEM — memory accesses and address instructions
Statement: A memory access is its kind (load, store, atomic read-modify-write, reduction, `ldu`,
  read-only proxy load, `discard` or `st.bulk`), its state space (none for a generic address),
  memory semantics, whether it is `.mmio`, scope, element type, vector length, the extension of a
  narrow element into a wider destination register, `.nc`, cache hints, address, destination
  registers and sources. An address instruction is a `cvta`, `mapa`, `isspacep`, `getctarank`,
  `prefetch`, `prefetchu` or `applypriority` with its state space, width and operands. Every entry
  of the `mem` family decodes to one of these, except the tensormap prefetch.

Defs: AtomOp, MemKind, MemExt, CacheHints, AddrBase, Addr, MemAccess, MemAccess.regs,
  MemAccess.locSpace?, Decode.MemAccess.ofRaw, Decode.MemAccess.space?, Decode.MemAccess.scope?,
  Decode.MemAccess.atomOp?, Decode.MemAccess.addrOf, Decode.MemAccess.loadDsts,
  Decode.MemAccess.storeSrcs, Decode.MemAccess.paramChecks, memTypeOk, vectorShapeOk, MemExt.ok,
  CacheHints.globalOnly,
  MemAccess.baseOk, MemAccess.weakOk, MemAccess.strongSemOk, MemAccess.strongOk, MemAccess.bulkOk,
  MemKind.atomOp?,
  MemAccess.atomicOk, MemAccess.atomicOk_of_vec_one, MemAccess.rule,
  AddrInstr, Decode.AddrInstr.ofRaw, Decode.AddrInstr.width?, AddrInstr.rule

Source:
- §9.7.10.8: "ld{.weak}{.ss}{.cop}{.level::cache_hint}{.level::prefetch_size}{.vec}.type d,
    [a]{.unified}{, cache_policy};"
- §9.7.10.8: ".ss = { .const, .global, .local, .param{::entry, ::func}, .shared{::cta, ::cluster}
    };"
- §9.7.10.8: "A destination register wider than the specified type may be used. The value loaded is
    sign-extended to the destination register width for signed integers, and is zero-extended to the
    destination register width for unsigned and bit-size types."
- §9.7.10.8: "For ld.param::entry instruction, operand a must be a kernel parameter address,
    otherwise behavior is undefined. For ld.param::func instruction, operand a must be a device
    function parameter address, otherwise behavior is undefined."
- §9.7.10.8: "ld.mmio.sem.sys{.global}.type d, [a];"
- §9.7.10.8: ".sem = { .acquire, .relaxed };"
- §9.7.10.11 (st): "st.mmio.sem.sys{.global}.type [a], b;"
- §9.7.10.11 (st): ".sem = { .release, .relaxed };"
- §8.4.1: "For formal specification of semantics of mmio operation from Memory Consistency Model
    perspective, it is equivalent to the semantics of a strong operation."
- §9.7.10.10 (ldu): "where the address is guaranteed to be the same across all threads in the warp."
- §9.7.10.14 (st.bulk)
- §9.7.10.16 (prefetch): "The .valid_addr qualifier requires at-least 1B-wide memory location
    referred to by address a to be valid for this access. Otherwise, the behavior is undefined."
- §9.7.10.17 (applypriority): "If the specified address does not fall within the address window of
    .global state space then the behavior is undefined."
- §9.7.10.20 (discard): "Semantically, this behaves like a weak write of an unstable indeterminate
    value : reads of memory locations with unstable indeterminate values may return different bit
    patterns each time until the memory is overwritten."
- §9.7.15.5 (atom): "If the .sem qualifier is absent, .relaxed is assumed by default."
- §9.7.15.5 (atom): ".vec_16_bit = { .v2, .v4, .v8 } .vec_32_bit = { .v2, .v4 };"
- §9.7.15.5 (atom): "For atom with vector type, operands d and b are brace-enclosed vector
    expressions, size of which is equal to the size of vector qualifier."
- §9.7.15.6 (red)
- §9.7.10.23 (cvta): "When converting a generic address into a const , Kernel Function Parameters (
    .param ), global , local , or shared address, the resulting address is undefined in cases where
    the generic address does not fall within the address window of the specified state space."
- §9.7.10.26 (mapa)
- §9.7.10.22 (isspacep)
- §9.7.10.27 (getctarank)
- §9.7.10.11 (st): "A source register wider than the specified type may be used."
- §5.1.7 (`.shared` is `.shared::cta`)
- §6.4.3: "when specified as destination operand, all elements in vector expression must be unique,
    otherwise behavior is undefined"
- §5.1.6.4: "ld.param.s32 %y, [buffer+8];"

Direction: representation

Applies: Every instruction of the `mem` family other than the tensormap prefetch

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at the widths
  of the operand types, except a wider value register of an integer store; a by-value parameter
  access lies inside the object and is aligned for every placement its declaration allows.

Effect: Representation; `MemAccess.rule` selects THREAD-ACCESS and THREAD-MOVE and `AddrInstr.rule`
  selects THREAD-CVTA, THREAD-SHARED-POINTER and THREAD-PREFETCH for the forms listed below, and no
  rule otherwise. `.shared` and `.shared::cta` are the same window (`.shared .cta`); `.param` and
  `.param::entry` are the kernel parameter space, `.param::func` the device function parameter
  space. An absent `.sem` is `.weak` for `ld` and `st` and `.relaxed` for `atom` and `red`. A
  load's destination registers have one width, the element
  width or a wider one (`MemExt`: zero-extended for `.b` and `.u` types, sign-extended for `.s`
  types; a floating element needs its own width). The value register of a `.b`, `.u` or `.s` store
  may be wider than the type (`storeSrcs`). Rejected at decoding: a destination vector naming a
  register twice or containing the sink `_`; a `ld.param` of a by-value parameter object that leaves
  the object or whose size does not divide the offset and the declared alignment; a `ld.param` of a
  scalar parameter at a nonzero offset, of a vector, at another width than the parameter's or wider
  than 64 bits. The rules are as follows. THREAD-ACCESS (`weakOk`) covers weak `ld` of the global,
  shared (`::cta`, `::cluster`), local and constant spaces and of a generic address, weak `st` of
  the global, shared and local spaces and of a generic address, of an element type `.b`, `.u`, `.s`
  of 8 to 128 bits or `.f32`, `.f64`, extended into a register of at most 64 bits; scalar, `.v2` and
  `.v4` of elements of at most 64 bits, `.v4` of 64-bit elements and `.v8` of 32-bit elements of a
  global or generic address; `ld.global.nc` scalar or vector; the eviction priorities, prefetch size
  and cache policy on a global or generic address; no `.lu` or `.cs` on a local load. Also
  (`strongOk`) the strong loads and stores of the same shapes: `.relaxed` and `.acquire` loads and
  `.relaxed` and `.release` stores at every scope of a global or shared space or a generic address,
  `.volatile` accesses of a global, shared or local space or a generic address, and scalar `.mmio`
  accesses at `.sys` of the global space or a generic address, `.relaxed` and `.acquire` loads and
  `.relaxed` and `.release` stores, which keep their `.sem` (§8.4.1: an mmio operation is a strong
  operation in the memory model); and (`bulkOk`) `st.bulk` of a `.shared::cta` or generic address
  with initial value 0. THREAD-MOVE: `ld.param` of the kernel parameter space through a parameter
  name or a register, extended as above. THREAD-ATOMIC (`atomicOk`): scalar `atom` and `red` of the
  operation and type combinations of Table 41 and Table 42 (`.b16` `cas`, `.b128` `exch` and `cas`,
  the floating `add` forms and the packed `.f16x2` and `.bf16x2` `add` included), of a global,
  shared or generic address, and vector `atom` and `red` of the vector table of §9.7.15.5 and
  §9.7.15.6 (`add`, `min` and `max` of `.v2`, `.v4` and `.v8` of `.f16` and `.bf16` and of `.v2` and
  `.v4` of `.f16x2` and `.bf16x2`, all with `.noftz`, and `add` of `.v2` and `.v4` of `.f32`), of a
  global or generic address, with every `.sem` the syntax allows and every `.scope`, and `atom` with
  `_` or with one destination register per vector element. Without a rule: `ldu` (its address must
  be uniform across the warp), the read-only proxy load, `discard` (an unstable indeterminate
  value), `.param::func` accesses (device function parameters are not modeled; an entry function's
  kernel parameter at a `.param::func` operand is undefined), `st.param`.
-/

/-- The operation of an atomic read-modify-write or reduction (§9.7.15.5). -/
inductive AtomOp where
  | and | or | xor | add | inc | dec | min | max | exch | cas
  deriving DecidableEq, Repr

/-- What a memory access does: a load or store (`ld`, `st`), an atomic read-modify-write
(`atom`), a reduction (`red`), a load of warp-uniform read-only data (`ldu`), a load through the
read-only proxy (`ld.proxy::readonly`), the discard of a cache line (`discard`) or the zero
initialization of a shared memory region (`st.bulk`). -/
inductive MemKind where
  | load | store
  | rmw (op : AtomOp)
  | reduce (op : AtomOp)
  | loadUniform
  | loadReadonly
  | discard
  | bulkInit
  deriving DecidableEq, Repr

/-- How a narrow loaded element fills a wider destination register of `w` bits. -/
inductive MemExt where
  | same
  | zero (w : Nat)
  | sign (w : Nat)
  deriving DecidableEq, Repr

/-- Cache qualifiers and the `cache_policy` operand; no rule reads them. -/
structure CacheHints where
  cop : Option Isa.Token := none
  l1 : Option Isa.Token := none
  l2 : Option Isa.Token := none
  prefetch : Option Isa.Token := none
  policy : Option Opnd := none
  deriving DecidableEq, Repr

/-- The base of an address: a register of `w` bits, the address of a `.shared` variable, a kernel
parameter (`object` for a by-value parameter object), an absolute address, or the address of a
`.local` or `.const` variable (its offset from the local or constant base). -/
inductive AddrBase where
  | reg (r w : Nat)
  | sharedSym (offset : Nat)
  | param (name : String) (object : Bool)
  | imm (a : Int)
  | localSym (offset : Nat)
  | constSym (offset : Nat)
  deriving DecidableEq, Repr

/-- An address `[base+off]`. -/
structure Addr where
  base : AddrBase
  off : Int := 0
  deriving DecidableEq, Repr

/-- A memory access. -/
structure MemAccess where
  kind : MemKind
  space : Option StateSpace
  sem : Sem
  scope : Option MbarScope := none
  elem : DType
  vec : Nat := 1
  ext : MemExt := .same
  nc : Bool := false
  noftz : Bool := false
  hints : CacheHints := {}
  addr : Addr
  dsts : List (Option Nat) := []
  srcs : List Opnd := []
  /-- The `.mmio` qualifier of `ld.mmio` and `st.mmio`; the access keeps its `.sem`. -/
  mmio : Bool := false
  deriving DecidableEq, Repr

/-- The named destination registers. -/
def MemAccess.regs (a : MemAccess) : List Nat := a.dsts.filterMap id

/-- The location space of a load or store that `memTmpl` performs directly (THREAD-ACCESS): a
global access through a 64-bit register or a `.shared::cta` access through a 32-bit register,
without extension and without cache hints. Every other access is located by `accessLoc`. -/
def MemAccess.locSpace? (a : MemAccess) : Option Space :=
  if (a.kind = .load ∨ a.kind = .store) ∧ a.ext = .same ∧ a.hints = {} then
    match a.space, a.addr.base with
    | some .global, .reg _ 64 => some .global
    | some (.shared .cta), .reg _ 32 => some .shared
    | _, _ => none
  else none

/-- An address conversion or query. -/
inductive AddrInstr where
  /-- `cvta{.to}.space.size d, a`; `toSpace` for `.to`. -/
  | cvta (toSpace : Bool) (space : StateSpace) (w : Nat) (d : Nat) (a : Opnd)
  /-- `mapa{.space}.size d, a, b`; `generic` without `.shared::cluster`. -/
  | mapa (generic : Bool) (w : Nat) (d : Nat) (a rank : Opnd)
  /-- `isspacep.space p, a`. -/
  | isspacep (space : StateSpace) (p : Nat) (a : Opnd)
  /-- `getctarank{.space}.size d, a`; `generic` without `.shared::cluster`. -/
  | getctarank (generic : Bool) (w : Nat) (d : Nat) (a : Opnd)
  /-- `prefetch{.space}.level [a]` and `prefetch.global.L2::evict_* [a]` (`space` none for a
  generic address), `prefetch{.global}.L1::32B.valid_addr [a]` (`validAddr`) and `prefetchu.L1 [a]`
  (`uniform`). -/
  | prefetch (space : Option StateSpace) (uniform validAddr : Bool) (a : Addr)
  /-- `applypriority{.global}.L2::evict_normal [a], 128`; `global` for `.global`. -/
  | applypriority (global : Bool) (a : Addr)
  deriving DecidableEq, Repr

namespace Decode
open PTX.Syntax

/-- The state space of a `.ss` token; `none` for a space without a representation. -/
def MemAccess.space? : Isa.Token → Option StateSpace
  | .global_ => some .global
  | .shared | .shared_cta => some (.shared .cta)
  | .shared_cluster => some (.shared .cluster)
  | .local_ => some .local
  | .param | .param_entry => some .param
  | .param_func => some .paramFunc
  | .const => some .const
  | _ => none

/-- The `.scope` qualifier of an access, `none` when it is absent. -/
def MemAccess.scope? : Option Isa.Token → M (Option MbarScope)
  | none => pure none
  | some .cta => pure (some .cta)
  | some .cluster => pure (some .cluster)
  | some .gpu => pure (some .gpu)
  | some .sys => pure (some .sys)
  | some _ => throw "scope"

/-- The operation of `atom` or `red`. -/
def MemAccess.atomOp? : Option Isa.Token → M AtomOp
  | some .and => pure .and | some .or => pure .or | some .xor => pure .xor
  | some .add => pure .add | some .inc => pure .inc | some .dec => pure .dec
  | some .min => pure .min | some .max => pure .max | some .exch => pure .exch
  | some .cas => pure .cas
  | _ => throw "atomic operation"

/-- The address operand: `[r]`, `[sym]`, `[imm]` or one of them with a signed constant offset;
a register keeps its declared width. -/
def MemAccess.addrOf (env : Env) : Operand → M Addr
  | .address [x] => do
    let (b, o) := match x with
      | .offset sg b (.literal t) => (b, some (sg, t))
      | b => (b, none)
    let off : Int ← match o with
      | none => pure 0
      | some (sg, t) => do
        let .imm v ← literal t | throw s!"bad offset {t}"
        if sg = "-" then pure (-v) else pure v
    let base ← match b with
      | .register r => do
        let w ← regWidth env.classes r
        pure (AddrBase.reg (← reg env w (.register r)) w)
      | .symbol s =>
        match env.shared.lookup s with
        | some o => pure (.sharedSym o)
        | none =>
          if let some o := env.locals.lookup s then pure (.localSym o)
          else if let some o := env.consts.lookup s then pure (.constSym o)
          else if (env.objects.find? (·.name = s)).isSome then pure (.param s true)
          else if (env.params.lookup s).isSome then pure (.param s false)
          else throw s!"unknown address symbol {s}"
      | .literal t => do
        let .imm v ← literal t | throw s!"bad address {t}"
        pure (.imm v)
      | _ => throw "unsupported address"
    return ⟨base, off⟩
  | o => throw s!"unsupported address {repr o}"

/-- The destinations of a load: registers of one width `dw`, the element width or wider (the
extension of `ext`), distinct (§6.4.3). -/
def MemAccess.loadDsts (env : Env) (elem : DType) (os : List Operand) :
    M (List (Option Nat) × MemExt) := do
  let widths ← os.mapM fun o => match o with
    | .register r => regWidth env.classes r
    | o => throw s!"expected register, got {repr o}"
  let some dw := widths.head? | throw "load without destination"
  unless widths.all (· = dw) do throw "destination registers of different widths"
  let ew := elem.width
  let ext ← if dw = ew then pure MemExt.same
    else if ew < dw then match elem with
      | .int .s _ => pure (.sign dw)
      | .int _ _ => pure (.zero dw)
      | _ => throw "wider destination of a floating element"
    else throw "destination narrower than the element"
  return ((← dstRegs env dw os).map some, ext)

/-- The value operands of a store (§9.7.10.11: "A source register wider than the specified type
may be used."): for a `.b`, `.u` or `.s` type a register of the type's width or wider, otherwise a
source of the type (`rsrcs`). -/
def MemAccess.storeSrcs (env : Env) (o : Isa.ROpnd) : M (List Opnd) := do
  let d ← ROpnd.dtype o
  let one (x : Operand) : M Opnd := match d, x with
    | .int _ w, .register r => match SReg.ofName? r with
      | none => do
        let (rw, i) ← regInfo env.classes r
        unless w ≤ rw do throw s!"register {r} has width {rw}, narrower than {w}"
        pure (.reg i)
      | some _ => typedOpnd env d x
    | _, x => typedOpnd env d x
  match o.op with
  | .vector cs => cs.mapM one
  | x => return [← one x]

/-- The decoding checks of `ld.param`: a by-value object access lies inside the object and its
size divides the offset and the declared alignment; a scalar parameter is read whole, at offset 0,
at its own width of at most 64 bits. -/
def MemAccess.paramChecks (env : Env) (a : MemAccess) : M Unit := do
  let w := a.elem.width
  match a.addr.base with
  | .param p true => do
    let some o := env.objects.find? (·.name = p) | throw s!"{p} is not a parameter object"
    unless 0 ≤ a.addr.off do throw s!"negative parameter offset"
    let off := a.addr.off.toNat
    let size := w / 8 * a.vec
    unless off + size ≤ o.bytes do throw s!"ld.param: outside parameter object {o.name}"
    unless o.alignment % size = 0 ∧ off % size = 0 do
      throw "ld.param: access not aligned to its size"
  | .param p false => do
    let some pw := env.params.lookup p | throw s!"unknown parameter {p}"
    unless a.addr.off = 0 ∧ a.vec = 1 do throw s!"{p} is not a parameter object"
    unless pw = w do throw s!"parameter {p} has width {pw}"
    unless w ≤ 64 do throw "ld.param: parameters wider than 64 bits"
  | _ => pure ()

/-- The memory access of a recognized `mem`-family instruction, or `none` when it has no
`MemAccess` representation this round. -/
def MemAccess.ofRaw (env : Env) (r : Isa.Raw) : M (Option MemAccess) := do
  let kind? : Option MemKind ← match r.entry with
    | .ld | .ld_vec | .ld_vec256 | .ld_param | .ld_param_vec => pure (some .load)
    | .ldu | .ldu_vec => pure (some .loadUniform)
    | .ld_proxy_readonly => pure (some .loadReadonly)
    | .st | .st_vec | .st_vec256 => pure (some .store)
    | .st_bulk => pure (some .bulkInit)
    | .discard => pure (some .discard)
    | .atom | .atom_cas | .atom_exch | .atom_half | .atom_vec_half | .atom_vec_f32
    | .atom_f32_noftz | .atom_vec_f32_noftz | .atom_bitbucket | .atom_cas_bitbucket
    | .atom_exch_bitbucket | .atom_half_bitbucket | .atom_vec_half_bitbucket
    | .atom_vec_f32_bitbucket | .atom_f32_noftz_bitbucket | .atom_vec_f32_noftz_bitbucket =>
      pure (some (MemKind.rmw (← MemAccess.atomOp? (r.get .op))))
    | .red | .red_half | .red_vec_half | .red_vec_f32 | .red_f32_noftz | .red_vec_f32_noftz =>
      pure (some (MemKind.reduce (← MemAccess.atomOp? (r.get .op))))
    | _ => pure none
  let some kind := kind? | return none
  let space? : Option (Option StateSpace) := match r.get .space with
    | none => some none
    | some t => (MemAccess.space? t).map some
  let some space := space? | return none
  let atomic := match kind with | .rmw _ | .reduce _ => true | _ => false
  let sem? : Option Sem := match r.get .sem, r.get .weak with
    | none, none => some (if atomic then .relaxed else .weak)
    | some .weak, _ | none, some _ => some .weak
    | some .relaxed, _ => some .relaxed
    | some .acquire, _ => some .acquire
    | some .release, _ => some .release
    | some .acq_rel, _ => some .acqRel
    | some .volatile, _ => some .volatile
    | _, _ => none
  let some sem := sem? | return none
  let scope ← MemAccess.scope? (r.get .scope)
  let elem ← match kind with
    | .bulkInit | .discard => pure (DType.int .b 8)
    | _ => dtype (r.get .type)
  let vec := match r.get .vec with
    | some .v2 => 2 | some .v4 => 4 | some .v8 => 8 | _ => 1
  let addrName := match r.entry with | .ld_param | .ld_param_vec => "a" | _ => "addr"
  let addr ← MemAccess.addrOf env (← arg r addrName)
  let policy ← match opnd? r "cache_policy" with
    | some o => some <$> src env 64 o.op
    | none => pure none
  let hints : CacheHints :=
    ⟨r.get .cop, r.get .l1ev, r.get .l2ev, r.get Isa.Slot.prefetch, policy⟩
  let (dsts, ext) ← match kind, opnd? r "d" with
    | .load, _ | .loadUniform, _ | .loadReadonly, _ =>
      MemAccess.loadDsts env elem (← args r "d")
    | _, some o =>
      if o.kind == .imm then pure ([none], MemExt.same)
      else (·, MemExt.same) <$> rdsts env o
    | _, none => pure ([], MemExt.same)
  let srcs ← match kind with
    | .bulkInit => do
      let o ← arg r "size"
      let w ← match o with
        | .register x => regWidth env.classes x
        | _ => pure 64
      unless w = 32 ∨ w = 64 do throw "st.bulk: size must be 32 or 64 bits"
      pure [← src env w o, ← src env 64 (← arg r "initval")]
    | .discard => do pure [← src env 64 (← arg r "size")]
    | _ => match opnd? r "compare", opnd? r "value" with
      | some c, some v => (· ++ ·) <$> rsrcs env c <*> rsrcs env v
      | none, some v => match kind with
        | .store => MemAccess.storeSrcs env v
        | _ => rsrcs env v
      | _, _ => pure []
  let nc := flag r Isa.Slot.nc
  let noftz := flag r Isa.Slot.noftz
  let a : MemAccess :=
    { kind := kind, space := space, sem := sem, scope := scope, elem := elem, vec := vec,
      ext := ext, nc := nc, noftz := noftz, hints := hints, addr := addr, dsts := dsts,
      srcs := srcs, mmio := flag r .mmio }
  if space = some .param then MemAccess.paramChecks env a
  return some a

/-- The width of an address instruction's `.size` type. -/
def AddrInstr.width? : Option Isa.Token → M Nat
  | some .u32 => pure 32
  | some .u64 => pure 64
  | _ => throw "address size"

/-- The address instruction of a recognized instruction, or `none` for a state space without
a representation. -/
def AddrInstr.ofRaw (env : Env) (r : Isa.Raw) : M (Option AddrInstr) := do
  match r.entry with
  | .cvta | .cvta_generic => do
    let some t := r.get .space | throw "cvta state space"
    let some sp := MemAccess.space? t | return none
    let w ← AddrInstr.width? (r.get .type)
    let toSpace := r.entry == .cvta
    let d ← reg env w (← arg r "d")
    let a ← src env w (← arg r (if toSpace then "ptr" else "a"))
    return some (.cvta toSpace sp w d a)
  | .mapa | .mapa_generic => do
    let w ← AddrInstr.width? (r.get .type)
    return some (.mapa (r.entry == .mapa_generic) w (← reg env w (← arg r "d"))
      (← src env w (← arg r "a")) (← src env 32 (← arg r "b")))
  | .isspacep => do
    let some t := r.get .space | throw "isspacep state space"
    let some sp := MemAccess.space? t | return none
    let .register a ← arg r "a" | throw "isspacep operand"
    let w ← regWidth env.classes a
    return some (.isspacep sp (← reg env 1 (← arg r "p")) (← src env w (.register a)))
  | .getctarank | .getctarank_generic => do
    let w ← AddrInstr.width? (r.get .type)
    return some (.getctarank (r.entry == .getctarank_generic) w (← reg env 32 (← arg r "d"))
      (← src env w (← arg r "a")))
  | .prefetch | .prefetch_valid_addr | .prefetchu => do
    if flag r .tensormap then return none
    let space ← match r.get .space with
      | none => pure none
      | some t => match MemAccess.space? t with
        | some sp => pure (some sp)
        | none => throw "prefetch state space"
    return some (.prefetch space (r.entry == .prefetchu) (r.entry == .prefetch_valid_addr)
      (← MemAccess.addrOf env (← arg r "addr")))
  | .applypriority =>
    return some (.applypriority (flag r .space) (← MemAccess.addrOf env (← arg r "addr")))
  | _ => throw "not an address instruction"

end Decode

/-- The `.type`s of `ld` and `st` with a rule: `.b`, `.u`, `.s` of 8 to 128 bits (`.b128`
only), `.f32` and `.f64`. -/
def memTypeOk : DType → Bool
  | .int .b w => [8, 16, 32, 64, 128].contains w
  | .int _ w => [8, 16, 32, 64].contains w
  | .float .f32 | .float .f64 => true
  | _ => false

/-- The `.vec` and `.type` combinations of a vector `ld`/`st` (§9.7.10.8, §9.7.10.11): elements
of at most 64 bits, and `.v4` of 64-bit elements only in the global space. -/
def vectorShapeOk (n w : Nat) (global : Bool) : Bool :=
  w ≤ 64 ∧ (n = 2 ∨ w ≤ 32 ∨ global)

/-- The extension of a load into its destination registers (§9.7.10.8): none, zero-extension of a
`.b` or `.u` element or sign-extension of a `.s` element, into registers of at most 64 bits. -/
@[simp] def MemExt.ok (ext : MemExt) (elem : DType) : Bool :=
  match ext, elem.kind? with
  | .same, _ => true
  | .zero dw, some .b | .zero dw, some .u => dw ≤ 64
  | .sign dw, some .s => dw ≤ 64
  | _, _ => false

/-- The cache hints that the manual supports only for global addresses: the eviction priorities,
the prefetch size and the cache policy (§9.7.10.2, §9.7.10.8). -/
@[simp] def CacheHints.globalOnly (h : CacheHints) : Bool :=
  h.l1.isSome || h.l2.isSome || h.prefetch.isSome || h.policy.isSome

/-- The address forms of a weak access with a rule: a 64-bit register or an absolute address for
the global space, a 32-bit or 64-bit register for the other spaces and for a generic address, a
`.shared` variable for a shared window, an absolute address for the local and constant spaces
and for a generic address, a `.local` variable for the local space and a `.const` variable for the
constant space. -/
@[simp] def MemAccess.baseOk (a : MemAccess) : Bool :=
  match a.space, a.addr.base with
  | some .global, .reg _ 64 | some .global, .imm _ => true
  | some (.shared _), .reg _ w | some .local, .reg _ w | some .const, .reg _ w
  | none, .reg _ w => w = 32 ∨ w = 64
  | some (.shared _), .sharedSym _ => true
  | some .local, .localSym _ | some .const, .constSym _ => true
  | some .local, .imm _ | some .const, .imm _ | none, .imm _ => true
  | _, _ => false

/-- A weak `ld` or `st` with a rule (THREAD-ACCESS): no scope, an element type of `memTypeOk`
and an extension of `MemExt.ok`; a load of the global, shared, local or constant space or of a
generic address, a store of the global, shared or local space or of a generic address; scalar,
`.v2` or `.v4` of elements of at most 64 bits (`.v4` of 64-bit elements and `.v8` of 32-bit
elements only for a global or generic address); `.nc` only on a global load; the cache hints
`globalOnly` only for a global or generic address, and `.lu` and `.cs` not on a local load. -/
@[simp] def MemAccess.weakOk (a : MemAccess) : Bool :=
  let w := a.elem.width
  let global := a.space == some .global
  let globalOrGeneric := global || a.space.isNone
  let spaceOk : Bool := match a.kind, a.space with
    | .load, some .global | .load, some (.shared _) | .load, some .local | .load, some .const
    | .load, none => true
    | .store, some .global | .store, some (.shared _) | .store, some .local | .store, none => true
    | _, _ => false
  let shape : Bool := a.vec = 1 ∨
    (w ≤ 64 ∧ (a.vec = 2 ∨ (a.vec = 4 ∧ (w ≤ 32 ∨ globalOrGeneric)))) ∨
    (a.vec = 8 ∧ w = 32 ∧ globalOrGeneric)
  let ncOk : Bool := !a.nc || (a.kind == .load && global)
  let hintOk : Bool := (!a.hints.globalOnly || globalOrGeneric) &&
    !(a.kind == .load && a.space == some .local &&
      (a.hints.cop == some .lu || a.hints.cop == some .cs))
  let count : Bool := match a.kind with
    | .load => a.dsts.length = a.vec ∧ a.dsts.all Option.isSome ∧ a.srcs = []
    | _ => a.srcs.length = a.vec ∧ a.dsts = []
  a.sem == .weak && a.scope.isNone && !a.mmio && !a.noftz && memTypeOk a.elem &&
    a.ext.ok a.elem && a.baseOk && spaceOk && shape && ncOk && hintOk && count

/-- The memory semantics, scope, state space and cache qualifiers of a strong `ld` or `st` with
a rule (THREAD-ACCESS, §9.7.10.8, §9.7.10.11): `.relaxed` or `.acquire` loads and `.relaxed` or
`.release` stores with a scope, of a global or shared space or a generic address, without a cache
operator; `.volatile` accesses without a scope of a global, shared or local space or a generic
address, with at most the prefetch size; scalar `.mmio` accesses at `.sys`, `.relaxed` or
`.acquire` loads and `.relaxed` or `.release` stores, of the global space or a generic address
without hints. -/
@[simp] def MemAccess.strongSemOk (a : MemAccess) : Bool :=
  let relAcqSpace : Bool := match a.space with
    | some .global | some (.shared _) | none => true
    | _ => false
  let volatileSpace : Bool := match a.space with
    | some .global | some (.shared _) | some .local | none => true
    | _ => false
  match a.mmio, a.kind, a.sem, a.scope with
  | false, .load, .relaxed, some _ | false, .load, .acquire, some _
  | false, .store, .relaxed, some _ | false, .store, .release, some _ =>
    relAcqSpace && a.hints.cop.isNone
  | false, .load, .volatile, none | false, .store, .volatile, none =>
    volatileSpace && a.hints.cop.isNone && a.hints.l1.isNone && a.hints.l2.isNone &&
      a.hints.policy.isNone
  | true, .load, .relaxed, some .sys | true, .load, .acquire, some .sys
  | true, .store, .relaxed, some .sys | true, .store, .release, some .sys =>
    (a.space == some .global || a.space.isNone) && a.hints == {} && a.vec = 1
  | _, _, _, _ => false

/-- A strong `ld` or `st` with a rule (THREAD-ACCESS): semantics, scope and space of
`strongSemOk`, no `.nc`, and the element type, extension, address, shape and operands of a weak
access with a rule (`weakOk`). -/
@[simp] def MemAccess.strongOk (a : MemAccess) : Bool :=
  a.strongSemOk && !a.nc &&
    ({ a with sem := .weak, scope := none, mmio := false } : MemAccess).weakOk

/-- A weak `st.bulk` with a rule (THREAD-ACCESS): a `.shared::cta` address in a register or a
`.shared` variable, or a generic address in a register, and the initial value 0. -/
@[simp] def MemAccess.bulkOk (a : MemAccess) : Bool :=
  let addrOk : Bool := match a.space, a.addr.base with
    | some (.shared .cta), .reg _ w | none, .reg _ w => w = 32 ∨ w = 64
    | some (.shared .cta), .sharedSym _ => true
    | _, _ => false
  let initOk : Bool := match a.srcs with
    | [_, .imm 0] => true
    | _ => false
  a.sem == .weak && a.scope.isNone && a.hints == {} && addrOk && initOk && a.dsts = []

/-- The operation of an `atom` or `red`. -/
def MemKind.atomOp? : MemKind → Option AtomOp
  | .rmw op | .reduce op => some op
  | _ => none

/-- An `atom` or `red` with a rule (THREAD-ATOMIC): a scalar access of an operation and type of
Table 41 (`atom`) or Table 42 (`red`) at a global or shared address or a generic address, or a
vector access (`.v2`, `.v4`, `.v8`) of an operation, vector length and type of the vector table of
§9.7.15.5 or §9.7.15.6 at a global address or a generic address; `.noftz` exactly where the table
requires it; `.relaxed` or `.release` semantics, and also `.acquire` or `.acq_rel` for `atom`; for
`atom` the sink or one destination register per vector element, and none for `red`; the compare
and swap operands of `cas` and one operand otherwise, each a vector of the access's length; no
cache qualifier other than `.L2::cache_hint`. -/
@[simp] def MemAccess.atomicOk (a : MemAccess) : Bool :=
  let isRmw : Bool := match a.kind with | .rmw _ => true | _ => false
  let scalarOpOk (op : AtomOp) : Bool := match a.elem with
    | .int .u 32 => [AtomOp.add, .inc, .dec, .min, .max].contains op
    | .int .s 32 | .int .u 64 => [AtomOp.add, .min, .max].contains op
    | .int .s 64 => [AtomOp.min, .max].contains op
    | .int .b 32 | .int .b 64 =>
      [AtomOp.and, .or, .xor].contains op || (isRmw && [AtomOp.exch, .cas].contains op)
    | .int .b 16 => isRmw && op == .cas
    | .int .b 128 => isRmw && [AtomOp.exch, .cas].contains op
    | .float .f32 => op == .add
    | .float .f64 => op == .add && !a.noftz
    | .float .f16 | .float .bf16 | .packed (.float .f16) 2 | .packed (.float .bf16) 2 =>
      op == .add && a.noftz
    | _ => false
  let vectorOpOk (op : AtomOp) : Bool := match a.elem with
    | .float .f16 | .float .bf16 =>
      [2, 4, 8].contains a.vec && [AtomOp.add, .min, .max].contains op && a.noftz
    | .packed (.float .f16) 2 | .packed (.float .bf16) 2 =>
      [2, 4].contains a.vec && [AtomOp.add, .min, .max].contains op && a.noftz
    | .float .f32 => [2, 4].contains a.vec && op == .add
    | _ => false
  let opOk : Bool := match a.kind.atomOp? with
    | some op => if a.vec = 1 then scalarOpOk op else vectorOpOk op
    | none => false
  let noftzOk : Bool := !a.noftz || match a.elem with
    | .float _ | .packed _ _ => true
    | _ => false
  let semOk : Bool := match a.sem with
    | .relaxed | .release => true
    | .acquire | .acqRel => isRmw
    | _ => false
  let spaceOk : Bool := match a.space with
    | some .global | none => true
    | some (.shared _) => a.vec = 1
    | _ => false
  let count : Bool :=
    (if isRmw then a.dsts = [none] ∨ (a.dsts.length = a.vec ∧ a.dsts.all Option.isSome)
      else a.dsts = []) ∧
      a.srcs.length = a.vec * (if a.kind.atomOp? = some .cas then 2 else 1)
  let hintOk : Bool := a.hints.cop.isNone && a.hints.l1.isNone && a.hints.l2.isNone &&
    a.hints.prefetch.isNone
  opOk && noftzOk && semOk && spaceOk && a.ext == .same && !a.nc && a.baseOk && count && hintOk

/-- A scalar `atom` or `red` (`vec = 1`) has the rule conditions it had before the vector forms
had a rule. -/
theorem MemAccess.atomicOk_of_vec_one {a : MemAccess} (h : a.vec = 1) :
    a.atomicOk =
      let isRmw : Bool := match a.kind with | .rmw _ => true | _ => false
      let opOk : Bool := match a.kind.atomOp? with
        | some op => match a.elem with
          | .int .u 32 => [AtomOp.add, .inc, .dec, .min, .max].contains op
          | .int .s 32 | .int .u 64 => [AtomOp.add, .min, .max].contains op
          | .int .s 64 => [AtomOp.min, .max].contains op
          | .int .b 32 | .int .b 64 =>
            [AtomOp.and, .or, .xor].contains op || (isRmw && [AtomOp.exch, .cas].contains op)
          | .int .b 16 => isRmw && op == .cas
          | .int .b 128 => isRmw && [AtomOp.exch, .cas].contains op
          | .float .f32 => op == .add
          | .float .f64 => op == .add && !a.noftz
          | .float .f16 | .float .bf16 | .packed (.float .f16) 2 | .packed (.float .bf16) 2 =>
            op == .add && a.noftz
          | _ => false
        | none => false
      let noftzOk : Bool := !a.noftz || match a.elem with
        | .float _ | .packed _ _ => true
        | _ => false
      let semOk : Bool := match a.sem with
        | .relaxed | .release => true
        | .acquire | .acqRel => isRmw
        | _ => false
      let spaceOk : Bool := match a.space with
        | some .global | some (.shared _) | none => true
        | _ => false
      let count : Bool :=
        (if isRmw then a.dsts.length = 1 else a.dsts = []) ∧
          a.srcs.length = (if a.kind.atomOp? = some .cas then 2 else 1)
      let hintOk : Bool := a.hints.cop.isNone && a.hints.l1.isNone && a.hints.l2.isNone &&
        a.hints.prefetch.isNone
      opOk && noftzOk && semOk && spaceOk && a.vec = 1 && a.ext == .same && !a.nc && a.baseOk &&
        count && hintOk := by
  have hd : ∀ ds : List (Option Nat),
      (ds = [none] ∨ (ds.length = 1 ∧ ds.all Option.isSome = true)) ↔ ds.length = 1 := by
    intro ds
    match ds with
    | [] => simp
    | [d] => cases d <;> simp
    | _ :: _ :: _ => simp
  obtain ⟨kind, space, sem, scope, elem, vec, ext, nc, noftz, hints, addr, dsts, srcs⟩ := a
  subst h
  cases space <;> try (rename_i sp; cases sp)
  all_goals simp only [atomicOk, hd, Nat.one_mul, ite_true]
  all_goals simp

/-- The rule of a memory access: THREAD-ACCESS for the weak loads and stores of `weakOk`, the
strong loads and stores of `strongOk` and the `st.bulk` of `bulkOk`;
THREAD-MOVE for `ld.param` of the kernel parameter space, through a parameter name or a register,
of an element type of `memTypeOk` with an extension of `MemExt.ok`; THREAD-ATOMIC for the `atom`
and `red` of `atomicOk`. Every other access has no rule. -/
def MemAccess.rule (a : MemAccess) : Option RuleId :=
  let w := a.elem.width
  match a.kind, a.space with
  | .load, some .param =>
    let base : Bool := match a.addr.base with
      | .param _ _ => true
      | .reg _ bw => bw = 32 ∨ bw = 64
      | _ => false
    if base && a.ext.ok a.elem && a.sem == .weak && a.scope.isNone && a.hints == {} && !a.nc &&
        a.dsts.all Option.isSome && memTypeOk a.elem && (a.vec = 1 ∨ vectorShapeOk a.vec w false)
    then some .threadMove else none
  | .load, _ | .store, _ =>
    if a.weakOk || a.strongOk then some .threadAccess else none
  | .bulkInit, _ => if a.bulkOk then some .threadAccess else none
  | .rmw _, _ | .reduce _, _ => if a.atomicOk then some .threadAtomic else none
  | _, _ => none

/-- The rule of an address instruction: THREAD-CVTA for `cvta{.to}.global.u64`, for `cvta{.to}`
of the parameter, shared, local and constant spaces and for `isspacep`, THREAD-SHARED-POINTER for
`mapa` and `getctarank`, THREAD-PREFETCH for `prefetch` and `prefetchu` without
`.valid_addr` and for `applypriority.global`. -/
def AddrInstr.rule : AddrInstr → Option RuleId
  | .cvta _ .global 64 _ _ | .cvta _ .param _ _ _ | .cvta _ (.shared _) _ _ _
  | .cvta _ .local _ _ _ | .cvta _ .const _ _ _ | .isspacep .. => some .threadCvta
  | .mapa .. | .getctarank .. => some .threadSharedPointer
  | .prefetch _ _ false _ => some .threadPrefetch
  | .applypriority true _ => some .threadPrefetch
  | _ => none

end PTX
