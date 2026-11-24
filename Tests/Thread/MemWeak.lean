-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode

/-!
# Weak memory accesses and address instructions (THREAD-ACCESS, THREAD-ADDR, THREAD-MOVE,
THREAD-CVTA, THREAD-SHARED-POINTER, THREAD-PREFETCH)

Which forms have a rule, where each address resolves, the extension of a narrow load, `st.bulk`,
`ld.param` through a register, `isspacep`, `getctarank`, the prefetches and the rejected cases.
-/

namespace PTX.Tests.MemWeak
noncomputable section

/-! ## Rules of decoded forms -/

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 4, 64⟩, ⟨"%rs".toList, 2, 16⟩,
      ⟨"%p".toList, 2, 1⟩],
    labels := [], params := [("s32", 32), ("s8", 8)], shared := [("sh", 16)],
    objects := [⟨"obj", 8, 12, 4⟩] }
private def R (s : String) : Syntax.Operand := .register s
private def A (s : String) : Syntax.Operand := .address [.register s]
private def I (s : String) : Syntax.Operand := .literal s
private def rule (op : String) (args : List Syntax.Operand) : Except String (Option RuleId) :=
  Op.rule <$> Decode.op env op args

-- Weak loads and stores of every state space and of a generic address.
example : rule "ld.u32" [R "%r0", A "%rd0"] = .ok (some .threadAccess) := rfl
example : rule "st.u32" [A "%rd0", R "%r0"] = .ok (some .threadAccess) := rfl
example : rule "ld.shared::cluster.u32" [R "%r0", A "%r1"] = .ok (some .threadAccess) := rfl
example : rule "ld.shared.u32" [R "%r0", A "%rd1"] = .ok (some .threadAccess) := rfl
example : rule "ld.shared.u32" [R "%r0", .address [.symbol "sh"]] = .ok (some .threadAccess) := rfl
example : rule "ld.local.u32" [R "%r0", A "%rd0"] = .ok (some .threadAccess) := rfl
example : rule "ld.local.u32" [R "%r0", .address [I "240"]] = .ok (some .threadAccess) := rfl
example : rule "st.local.u32" [A "%rd0", R "%r0"] = .ok (some .threadAccess) := rfl
example : rule "ld.const.u32" [R "%r0", A "%rd0"] = .ok (some .threadAccess) := rfl
-- Sign and zero extension into a wider register.
example : rule "ld.global.s8" [R "%r0", A "%rd0"] = .ok (some .threadAccess) := rfl
example : rule "ld.global.u8" [R "%rs0", A "%rd0"] = .ok (some .threadAccess) := rfl
-- 256-bit vectors, cache hints, `.nc` vectors.
example : rule "ld.global.v4.u64" [.vector [R "%rd0", R "%rd1", R "%rd2", R "%rd3"], A "%rd0"] =
    .ok (some .threadAccess) := rfl
example : rule "ld.v4.u64" [.vector [R "%rd0", R "%rd1", R "%rd2", R "%rd3"], A "%rd0"] =
    .ok (some .threadAccess) := rfl
example : rule "ld.global.L2::cache_hint.u32" [R "%r0", A "%rd0", R "%rd1"] =
    .ok (some .threadAccess) := rfl
example : rule "ld.global.L2::64B.u32" [R "%r0", A "%rd0"] = .ok (some .threadAccess) := rfl
example : rule "ld.global.cg.u32" [R "%r0", A "%rd0"] = .ok (some .threadAccess) := rfl
example : rule "ld.global.nc.v4.u32" [.vector [R "%r0", R "%r1", R "%r2", R "%r3"], A "%rd0"] =
    .ok (some .threadAccess) := rfl
-- `st.bulk`, `ld.param` with extension, address instructions and prefetches.
example : rule "st.bulk.weak.shared::cta" [A "%r0", R "%r1", I "0"] =
    .ok (some .threadAccess) := rfl
example : rule "st.bulk" [A "%rd0", R "%rd1", I "0"] = .ok (some .threadAccess) := rfl
example : rule "ld.param.s32" [R "%rd0", .address [.symbol "s32"]] = .ok (some .threadMove) := rfl
example : rule "ld.param.u32" [R "%r0", A "%rd0"] = .ok (some .threadMove) := rfl
example : rule "isspacep.global" [R "%p0", R "%rd0"] = .ok (some .threadCvta) := rfl
example : rule "getctarank.u64" [R "%r0", R "%rd0"] = .ok (some .threadSharedPointer) := rfl
example : rule "cvta.global.u64" [R "%rd0", R "%rd1"] = .ok (some .threadCvta) := rfl
example : rule "cvta.local.u64" [R "%rd0", R "%rd1"] = .ok (some .threadCvta) := rfl
example : rule "cvta.to.local.u64" [R "%rd0", R "%rd1"] = .ok (some .threadCvta) := rfl
example : rule "cvta.const.u64" [R "%rd0", R "%rd1"] = .ok (some .threadCvta) := rfl
example : rule "cvta.to.const.u32" [R "%r0", R "%r1"] = .ok (some .threadCvta) := rfl
example : rule "cvta.to.param.u64" [R "%rd0", R "%rd1"] = .ok (some .threadCvta) := rfl
example : rule "cvta.shared.u64" [R "%rd0", R "%rd1"] = .ok (some .threadCvta) := rfl
example : rule "prefetch.global.L2" [A "%rd0"] = .ok (some .threadPrefetch) := rfl
example : rule "prefetch.local.L1" [A "%rd0"] = .ok (some .threadPrefetch) := rfl
example : rule "prefetchu.L1" [A "%rd0"] = .ok (some .threadPrefetch) := rfl
example : rule "applypriority.global.L2::evict_normal" [A "%rd0", I "128"] =
    .ok (some .threadPrefetch) := rfl

-- Decoded without a rule: `.lu`/`.cs` local loads, `.param::func`, strong and volatile accesses,
-- `ldu`, the read-only proxy, `discard`, `.valid_addr`, a generic `applypriority`, a 32-bit
-- global `cvta`.
example : rule "ld.local.lu.u32" [R "%r0", A "%rd0"] = .ok none := rfl
example : rule "ld.local.cs.u32" [R "%r0", A "%rd0"] = .ok none := rfl
example : rule "ld.param::func.u32" [R "%r0", .address [.symbol "s32"]] = .ok none := rfl
-- Strong loads have THREAD-ACCESS (`strongOk`).
example : rule "ld.volatile.global.u32" [R "%r0", A "%rd0"] = .ok (some .threadAccess) := rfl
example : rule "ld.relaxed.gpu.global.u32" [R "%r0", A "%rd0"] = .ok (some .threadAccess) := rfl
example : rule "ldu.global.u32" [R "%r0", A "%rd0"] = .ok none := rfl
example : rule "ld.global.u32.proxy::readonly" [R "%r0", A "%rd0"] = .ok none := rfl
example : rule "discard.global.L2" [A "%rd0", I "128"] = .ok none := rfl
example : rule "prefetch.global.L1::32B.valid_addr" [A "%rd0"] = .ok none := rfl
example : rule "applypriority.L2::evict_normal" [A "%rd0", I "128"] = .ok none := rfl
example : rule "cvta.global.u32" [R "%r0", R "%r1"] = .ok none := rfl
-- Rejected at decoding: a sink in a load vector, a wide element in a narrow register.
example : (rule "ld.global.v8.f32" [.vector [R "%r0", .sink, R "%r2", R "%r3", R "%r0", R "%r1",
    R "%r2", R "%r3"], A "%rd0"]).toOption = none := rfl
example : rule "ld.global.b128" [R "%rd0", A "%rd0"] =
    .error "destination narrower than the element" := rfl

/-! ## Where an access resolves (THREAD-ADDR) -/

/-- Grid of 4 CTAs of 32 threads in clusters of 2; thread 33 is in CTA 1, rank 1 of cluster 0. -/
private def L : Launch :=
  { grid := 4, block := 32, clusterSize := 2, params := fun p => if p = "s" then some 0xffffffff
      else none,
    paramObjects := fun p => if p = "obj" then some (⟨"obj", 8, 12, 4⟩, 0) else none,
    paramBytes := fun p k => if p = "obj" then some (BitVec.ofNat 8 (if k = 0 then 255 else k))
      else none }

private def regs : Nat → Option Value
  | 1 => some (.bits 64 0x1000)
  | 2 => some (.ptr 64 true (.shared 1 1) 16)
  | 3 => some (.ptr 64 true (.shared 1 0) 16)
  | 4 => some (.ptr 64 true (.shared 0 0) 16)
  | 5 => some (.bits 32 0x40)
  | 6 => some (.ptr 64 true (.param "obj") 0)
  | 7 => some (.ptr 32 false (.shared 1 0) 8)
  | 8 => some (.bits 64 0x1002)
  | 9 => some (.bits 64 0x40)
  | 10 => some (.ptr 64 false (.param "obj") 0)
  | 11 => some (.bits 32 16)
  | 12 => some (.bits 32 12)
  | 13 => some (.bits 64 0x100000000)
  | 14 => some (.ptr 64 false (.param "s") 0)
  | 15 => some (.ptr 64 true (.local 33) 16)
  | 16 => some (.ptr 64 true (.local 5) 16)
  | 17 => some (.ptr 64 true .const 32)
  | 18 => some (.ptr 64 false (.param "obj") 4)
  | 19 => some (.ptr 32 false (.param "obj") 0)
  | _ => none

private def t : TState := { regs := regs }

private def load (space : Option StateSpace) (base : AddrBase) (off : Int := 0)
    (elem : DType := .int .u 32) (vec : Nat := 1) (hints : CacheHints := {}) : MemAccess :=
  { kind := .load, space := space, sem := .weak, elem := elem, vec := vec, hints := hints,
    addr := ⟨base, off⟩, dsts := (List.range vec).map (fun j => some (20 + j)) }

private def readAt : Tmpl → Option Acc
  | .read a _ => some a
  | _ => none
private def writeAt : Tmpl → Option (Acc × List Byte)
  | .write a bs _ => some (a, bs)
  | _ => none
private def ubOf : Tmpl → Option Fault
  | .ub f => some f
  | _ => none

private def tmpl (a : MemAccess) (u : TState := t) : Tmpl := memTmpl [] L 33 u a

-- A 64-bit generic number is a global address (EXT-CVTA).
example : readAt (tmpl (load none (.reg 1 64))) = some { loc := ⟨.global, 0, 0x1000⟩, size := 4 } :=
  rfl
-- A generic shared pointer resolves in the shared window: its own CTA, or a peer of the cluster.
example : readAt (tmpl (load none (.reg 2 64) 4)) = some { loc := ⟨.shared, 1, 20⟩, size := 4 } :=
  rfl
example : readAt (tmpl (load none (.reg 3 64))) = some { loc := ⟨.shared, 0, 16⟩, size := 4 } :=
  rfl
-- A generic pointer produced in another CTA, a 32-bit generic number, a generic parameter pointer
-- and an offset leaving the shared window have no rule.
example : ubOf (tmpl (load none (.reg 4 64))) = some .noRule := rfl
example : ubOf (tmpl (load none (.reg 5 32))) = some .noRule := rfl
example : ubOf (tmpl (load none (.reg 6 64))) = some .noRule := rfl
example : ubOf (tmpl (load none (.reg 2 64) (-20))) = some .noRule := rfl
-- Local addresses name the issuing thread's own local memory; constant addresses the constant
-- memory.
example : readAt (tmpl (load (some .local) (.reg 1 64))) =
    some { loc := ⟨.local, 33, 0x1000⟩, size := 4 } := rfl
example : readAt (tmpl (load (some .local) (.imm 240))) =
    some { loc := ⟨.local, 33, 240⟩, size := 4 } := rfl
example : readAt (tmpl (load (some .const) (.reg 1 64) 8)) =
    some { loc := ⟨.const, 0, 0x1008⟩, size := 4 } := rfl
-- `.shared::cluster` takes a cluster pointer; `.shared::cta` does not.
example : readAt (tmpl (load (some (.shared .cluster)) (.reg 7 32) 4)) =
    some { loc := ⟨.shared, 0, 12⟩, size := 4 } := rfl
example : ubOf (tmpl (load (some (.shared .cta)) (.reg 7 32))) = some .noRule := rfl
-- A `.shared::cta` number in a 64-bit register must lie below `2 ^ 32`.
example : readAt (tmpl (load (some (.shared .cta)) (.reg 9 64))) =
    some { loc := ⟨.shared, 1, 0x40⟩, size := 4 } := rfl
example : ubOf (tmpl (load (some (.shared .cta)) (.reg 13 64))) = some .noRule := rfl
-- A `.shared` variable is in the thread's CTA.
example : readAt (tmpl (load (some (.shared .cta)) (.sharedSym 8) 4)) =
    some { loc := ⟨.shared, 1, 12⟩, size := 4 } := rfl
-- Alignment (§5.4.5).
example : ubOf (tmpl (load none (.reg 8 64))) = some .misaligned := rfl
-- `.v8` and `.v4` of 64-bit elements, and the global cache hints, need a global location.
example : readAt (tmpl (load none (.reg 1 64) (elem := .int .b 32) (vec := 8)) { t with sub := 3 })
    = some { loc := ⟨.global, 0, 0x100c⟩, size := 4, elem := 3 } := rfl
example : ubOf (tmpl (load none (.reg 2 64) (elem := .int .b 32) (vec := 8))) = some .noRule := rfl
example : ubOf (tmpl (load none (.reg 2 64) (hints := { policy := some (.reg 1) }))) =
    some .noRule := rfl
example : readAt (tmpl (load none (.reg 1 64) (hints := { policy := some (.reg 1) }))) =
    some { loc := ⟨.global, 0, 0x1000⟩, size := 4 } := rfl

-- `ld.global.nc` vectors read outside the memory model only at a site an assumption allows.
private def ncA : Assumption := { name := "nc", statement := "", ncLoads := fun _ => true }
private def readNCAt : Tmpl → Option Acc
  | .readNC a _ => some a
  | _ => none
example : readNCAt (memTmpl [ncA] L 33 t
    { (load (some .global) (.reg 1 64) (vec := 4)) with nc := true }) =
    some { loc := ⟨.global, 0, 0x1000⟩, size := 4 } := rfl
example : ubOf (tmpl { (load (some .global) (.reg 1 64) (vec := 4)) with nc := true }) =
    some .noRule := rfl

-- A generic store writes the bytes of its source.
private def store : MemAccess :=
  { kind := .store, space := none, sem := .weak, elem := .int .u 32, addr := ⟨.reg 2 64, 0⟩,
    srcs := [.reg 12] }
example : writeAt (tmpl store) =
    some ({ loc := ⟨.shared, 1, 16⟩, size := 4 }, (Value.bits 32 12).toBytes) := rfl

/-! ## Extension of a narrow load (§9.7.10.8) -/

example : extendLoaded (.sign 32) 8 (.bits 8 0xff) = .ok (.bits 32 0xffffffff) := rfl
example : extendLoaded (.zero 32) 8 (.bits 8 0xff) = .ok (.bits 32 0xff) := rfl
example : extendLoaded (.sign 64) 16 (.bits 16 0x7fff) = .ok (.bits 64 0x7fff) := rfl
example : extendLoaded (.sign 64) 16 (.bits 16 0x8000) = .ok (.bits 64 0xffffffffffff8000) := rfl
-- A loaded pointer has no bit pattern to extend.
example : extendLoaded (.zero 64) 32 (.ptr 32 false (.shared 0 0) 0) = .error .typeMismatch := rfl

/-! ## `st.bulk` (§9.7.10.14) -/

private def bulk (space : Option StateSpace) (base : AddrBase) (size : Opnd) : MemAccess :=
  { kind := .bulkInit, space := space, sem := .weak, elem := .int .b 8, addr := ⟨base, 0⟩,
    srcs := [size, .imm 0] }

example : writeAt (tmpl (bulk (some (.shared .cta)) (.reg 5 32) (.reg 11))) =
    some ({ loc := ⟨.shared, 1, 0x40⟩, size := 16 }, List.replicate 16 (.bits 8 0, 0)) := rfl
example : writeAt (tmpl (bulk none (.reg 2 64) (.imm 8))) =
    some ({ loc := ⟨.shared, 1, 16⟩, size := 8 }, List.replicate 8 (.bits 8 0, 0)) := rfl
-- A size that is not a multiple of 8, a global address and another CTA's window are undefined.
example : ubOf (tmpl (bulk (some (.shared .cta)) (.reg 5 32) (.reg 12))) = some .badValue := rfl
example : ubOf (tmpl (bulk none (.reg 1 64) (.imm 8))) = some .badValue := rfl
example : ubOf (tmpl (bulk none (.reg 3 64) (.imm 8))) = some .badValue := rfl
-- The access size of a `st.bulk` is its size, and its address must be a multiple of it (§6.4.1):
-- 64 bytes at `0x40` are aligned, 24 bytes at `0x40` and 24 bytes at 16 are not.
example : writeAt (tmpl (bulk (some (.shared .cta)) (.reg 5 32) (.imm 64))) =
    some ({ loc := ⟨.shared, 1, 0x40⟩, size := 64 }, List.replicate 64 (.bits 8 0, 0)) := rfl
example : ubOf (tmpl (bulk (some (.shared .cta)) (.reg 5 32) (.imm 24))) = some .misaligned := rfl
example : ubOf (tmpl (bulk none (.reg 2 64) (.imm 24))) = some .misaligned := rfl

-- Forms without a rule perform `ub noRule`.
example : ubOf (tmpl { (load none (.reg 1 64)) with kind := .loadUniform }) = some .noRule := rfl
example : ubOf (tmpl { (load none (.reg 1 64)) with kind := .discard }) = some .noRule := rfl
example : ubOf (tmpl { (load none (.reg 1 64)) with sem := .release, scope := some .gpu }) =
    some .noRule := rfl

/-! ## `ld.param` (THREAD-MOVE) -/

private def ldParam (base : AddrBase) (off : Int) (elem : DType) (ext : MemExt := .same) :
    MemAccess :=
  { kind := .load, space := some .param, sem := .weak, elem := elem, ext := ext,
    addr := ⟨base, off⟩, dsts := [some 20] }

-- A scalar parameter sign-extended into a wider register.
example : (execLocal L 33 t (.mem (ldParam (.param "s" false) 0 (.int .s 32) (.sign 64)))).map
    (·.regs 20) = .ok (some (.bits 64 0xffffffffffffffff)) := rfl
example : (execLocal L 33 t (.mem (ldParam (.param "s" false) 0 (.int .u 32) (.zero 64)))).map
    (·.regs 20) = .ok (some (.bits 64 0xffffffff)) := rfl
-- A parameter object through a register holding its parameter-space address.
example : (execLocal L 33 t (.mem (ldParam (.reg 10 64) 4 (.int .b 32)))).map (·.regs 20) =
    .ok (some (.bits 32 0x07060504)) := rfl
example : (execLocal L 33 t (.mem (ldParam (.reg 10 64) 0 (.int .s 8) (.sign 32)))).map
    (·.regs 20) = .ok (some (.bits 32 0xffffffff)) := rfl
-- Outside the object, misaligned, not a parameter address, a scalar parameter through a register.
example : (execLocal L 33 t (.mem (ldParam (.reg 10 64) 12 (.int .b 32)))).map (·.pc) =
    .error .badParam := rfl
example : (execLocal L 33 t (.mem (ldParam (.reg 10 64) 2 (.int .b 32)))).map (·.pc) =
    .error .misaligned := rfl
example : (execLocal L 33 t (.mem (ldParam (.reg 1 64) 0 (.int .b 32)))).map (·.pc) =
    .error .badParam := rfl
example : (execLocal L 33 t (.mem (ldParam (.reg 14 64) 0 (.int .b 32)))).map (·.pc) =
    .error .noRule := rfl
-- A parameter pointer away from the base of its object is not a kernel parameter address.
example : (execLocal L 33 t (.mem (ldParam (.reg 18 64) 0 (.int .b 32)))).map (·.pc) =
    .error .badParam := rfl

/-! ## A 128-bit parameter element (THREAD-MOVE, THREAD-BYTES)

`.param .align 16 .b8 P[16]` with byte 8 equal to 1 and every other byte 0. `ld.param.b128` reads
the 16 bytes as two 64-bit halves, low half first, through the parameter name and through a
register, and `mov.b128 {lo, hi}` then gives `lo = 0`, `hi = 1`. -/

private def wideEnv : Decode.Env :=
  { classes := [⟨"%rd".toList, 4, 64⟩, ⟨"%q".toList, 2, 128⟩], labels := [], params := [],
      objects := [⟨"P", 8, 16, 16⟩] }
example : (Op.rule <$> Decode.op wideEnv "ld.param.b128" [R "%q0", .address [.symbol "P"]]) =
    .ok (some .threadMove) := rfl
example : (Op.rule <$> Decode.op wideEnv "ld.param.b128" [R "%q0", A "%rd0"]) =
    .ok (some .threadMove) := rfl
-- A `.b128` element in a 64-bit register, or at an offset its size does not divide, is rejected.
example : (Decode.op wideEnv "ld.param.b128" [R "%rd0", .address [.symbol "P"]]).isOk = false :=
  rfl
example : (Decode.op wideEnv "ld.param.b128" [R "%q0", .address [.offset "+" (.symbol "P")
    (.literal "8")]]).isOk = false := rfl

private def wideL : Launch :=
  { grid := 1, block := 32, params := fun _ => none,
    paramObjects := fun p => if p = "P" then some (⟨"P", 8, 16, 16⟩, 0) else none,
    paramBytes := fun p k => if p = "P" ∧ k < 16 then some (if k = 8 then 1 else 0) else none }

private def wideT : TState :=
  { regs := fun r => if r = 1 then some (.ptr 64 false (.param "P") 0) else none }

private def unpack : Op := .move ⟨.unpack, .int .b 128, [some 3, some 4], [.reg 2]⟩

private def halves (base : AddrBase) : Exec (Option Value × Option Value) := do
  let u ← execLocal wideL 0 wideT (.mem (ldParam base 0 (.int .b 128)))
  let u := { u with regs := fun r => if r = 2 then u.regs 20 else u.regs r }
  let v ← execLocal wideL 0 u unpack
  pure (v.regs 3, v.regs 4)

example : halves (.param "P" true) = .ok (some (.bits 64 0), some (.bits 64 1)) := by rfl
example : halves (.reg 1 64) = .ok (some (.bits 64 0), some (.bits 64 1)) := by rfl

/-! ## `isspacep`, `getctarank`, `cvta.global` (THREAD-CVTA, THREAD-SHARED-POINTER) -/

private def pred (op : AddrInstr) : Exec (Option Value) :=
  (execLocal L 33 t (.addr op)).map (·.regs 30)

example : pred (.isspacep (.shared .cta) 30 (.reg 2)) = .ok (some (.pred true)) := rfl
example : pred (.isspacep (.shared .cta) 30 (.reg 3)) = .ok (some (.pred false)) := rfl
example : pred (.isspacep (.shared .cluster) 30 (.reg 3)) = .ok (some (.pred true)) := rfl
example : pred (.isspacep .global 30 (.reg 2)) = .ok (some (.pred false)) := rfl
example : pred (.isspacep .param 30 (.reg 6)) = .ok (some (.pred true)) := rfl
example : pred (.isspacep .global 30 (.reg 6)) = .ok (some (.pred true)) := rfl
example : pred (.isspacep (.shared .cta) 30 (.reg 6)) = .ok (some (.pred false)) := rfl
-- A generic shared pointer lies outside the local and constant windows (§6.4.1.1, §9.7.10.22).
example : pred (.isspacep .local 30 (.reg 2)) = .ok (some (.pred false)) := rfl
example : pred (.isspacep .const 30 (.reg 2)) = .ok (some (.pred false)) := rfl
-- A number, the device function parameter window, a pointer of another CTA: no rule.
example : pred (.isspacep .global 30 (.reg 1)) = .error .noRule := rfl
example : pred (.isspacep .paramFunc 30 (.reg 2)) = .error .noRule := rfl
example : pred (.isspacep (.shared .cta) 30 (.reg 4)) = .error .noRule := rfl

example : pred (.getctarank true 64 30 (.reg 3)) = .ok (some (.bits 32 0)) := rfl
example : pred (.getctarank true 64 30 (.reg 2)) = .ok (some (.bits 32 1)) := rfl
example : pred (.getctarank false 32 30 (.reg 7)) = .ok (some (.bits 32 0)) := rfl
example : pred (.getctarank false 32 30 (.reg 5)) = .ok (some (.bits 32 1)) := rfl
example : pred (.getctarank true 64 30 (.reg 1)) = .error .noRule := rfl

example : pred (.cvta false .global 64 30 (.reg 1)) = .ok (some (.bits 64 0x1000)) := rfl

/-! ## A store from a wider source register (THREAD-ACCESS, §9.7.10.11)

The low bits of the register are stored, through the direct and the located paths. -/

example : rule "st.global.b32" [A "%rd0", R "%rd1"] = .ok (some .threadAccess) := rfl
example : rule "st.u16" [A "%rd0", R "%r1"] = .ok (some .threadAccess) := rfl
example : rule "st.global.v2.u8" [A "%rd0", .vector [R "%r0", R "%rs1"]] =
    .ok (some .threadAccess) := rfl
-- A narrower register, and a wider one at a floating type, are rejected at decoding.
example : (rule "st.global.b64" [A "%rd0", R "%r1"]).isOk = false := rfl
example : (rule "st.global.f32" [A "%rd0", R "%rd1"]).isOk = false := rfl

private def st (space : Option StateSpace) (base : AddrBase) (elem : DType) (src : Opnd) :
    MemAccess :=
  { kind := .store, space := space, sem := .weak, elem := elem, addr := ⟨base, 0⟩,
    srcs := [src] }

example : writeAt (tmpl (st (some .global) (.reg 1 64) (.int .u 32) (.reg 9))) =
    some ({ loc := ⟨.global, 0, 0x1000⟩, size := 4 }, (Value.bits 32 0x40).toBytes) := rfl
example : writeAt (tmpl (st none (.reg 2 64) (.int .b 8) (.reg 12))) =
    some ({ loc := ⟨.shared, 1, 16⟩, size := 1 }, (Value.bits 8 12).toBytes) := rfl
example : writeAt (tmpl (st (some .global) (.reg 1 64) (.int .u 32) (.reg 13))) =
    some ({ loc := ⟨.global, 0, 0x1000⟩, size := 4 }, (Value.bits 32 0).toBytes) := rfl
-- A wider pointer has no bits to store; a narrower source is a type mismatch.
example : ubOf (tmpl (st (some .global) (.reg 1 64) (.int .u 32) (.reg 2))) =
    some .typeMismatch := rfl
example : ubOf (tmpl (st (some .global) (.reg 1 64) (.int .u 64) (.reg 12))) =
    some .typeMismatch := rfl

/-! ## Generic local and constant pointers (THREAD-CVTA)

Register 15 is a generic local pointer of thread 33 (the issuing thread), 16 one of thread 5 and
17 a generic constant pointer. -/

example : pred (.cvta false .local 64 30 (.reg 1)) =
    .ok (some (.ptr 64 true (.local 33) 0x1000)) := rfl
example : pred (.cvta true .local 64 30 (.reg 15)) = .ok (some (.bits 64 16)) := rfl
example : pred (.cvta false .const 64 30 (.reg 1)) = .ok (some (.ptr 64 true .const 0x1000)) := rfl
example : pred (.cvta true .const 64 30 (.reg 17)) = .ok (some (.bits 64 32)) := rfl
-- Another thread's local pointer has no rule; an address outside the window is a fault.
example : pred (.cvta true .local 64 30 (.reg 16)) = .error .noRule := rfl
example : pred (.cvta true .local 64 30 (.reg 1)) = .error .badValue := rfl
example : pred (.cvta true .local 64 30 (.reg 2)) = .error .badValue := rfl
example : pred (.cvta true .const 64 30 (.reg 15)) = .error .badValue := rfl
-- `isspacep`.
example : pred (.isspacep .local 30 (.reg 15)) = .ok (some (.pred true)) := rfl
example : pred (.isspacep .global 30 (.reg 15)) = .ok (some (.pred false)) := rfl
example : pred (.isspacep .const 30 (.reg 17)) = .ok (some (.pred true)) := rfl
example : pred (.isspacep .param 30 (.reg 17)) = .ok (some (.pred false)) := rfl
-- A generic local or constant pointer lies outside the other windows: `isspacep` answers 0
-- (§9.7.10.22: "with 0 otherwise"), e.g. `cvta.local.u64 %rdl, loc; isspacep.shared::cta.b32 %p,
-- %rdl;` sets `%p` to 0.
example : pred (.isspacep (.shared .cta) 30 (.reg 15)) = .ok (some (.pred false)) := rfl
example : pred (.isspacep (.shared .cluster) 30 (.reg 15)) = .ok (some (.pred false)) := rfl
example : pred (.isspacep .const 30 (.reg 15)) = .ok (some (.pred false)) := rfl
example : pred (.isspacep .local 30 (.reg 17)) = .ok (some (.pred false)) := rfl
example : pred (.isspacep (.shared .cta) 30 (.reg 17)) = .ok (some (.pred false)) := rfl
example : pred (.isspacep (.shared .cluster) 30 (.reg 17)) = .ok (some (.pred false)) := rfl
-- Another thread's local pointer, and the device function parameter window: no rule.
example : pred (.isspacep .local 30 (.reg 16)) = .error .noRule := rfl
example : pred (.isspacep (.shared .cta) 30 (.reg 16)) = .error .noRule := rfl
example : pred (.isspacep .paramFunc 30 (.reg 15)) = .error .noRule := rfl
-- Offsets (THREAD-POINTER-OFFSET).
example : (execLocal L 33 t (.int ⟨.add, .int .u 64, false, [some 30], [.reg 15, .imm 8]⟩)).map
    (·.regs 30) = .ok (some (.ptr 64 true (.local 33) 24)) := rfl
example : (execLocal L 33 t (.int ⟨.sub, .int .u 64, false, [some 30], [.reg 17, .imm 8]⟩)).map
    (·.regs 30) = .ok (some (.ptr 64 true .const 24)) := rfl
example : (execLocal L 33 t (.int ⟨.sub, .int .u 64, false, [some 30], [.reg 15, .imm 32]⟩)).map
    (·.regs 30) = .error .noRule := rfl
-- `cvt` of a pointer (THREAD-CVT): at its own width it keeps the pointer, and from 32 to 64 bits
-- it keeps a parameter-space pointer. A generic pointer at another width and a parameter-space
-- pointer narrowed to 32 bits have no rule.
private def cvtU (dw sw r : Nat) : Exec (Option Value) :=
  (execLocal L 33 t (.cvt { dst := .int .u dw, src := .int .u sw, d := 30, srcs := [.reg r] })).map
    (·.regs 30)
example : cvtU 64 64 15 = .ok (some (.ptr 64 true (.local 33) 16)) := rfl
example : cvtU 64 64 17 = .ok (some (.ptr 64 true .const 32)) := rfl
example : cvtU 64 64 6 = .ok (some (.ptr 64 true (.param "obj") 0)) := rfl
example : cvtU 64 32 19 = .ok (some (.ptr 64 false (.param "obj") 0)) := rfl
example : cvtU 32 64 15 = .error .noRule := rfl
example : cvtU 32 64 6 = .error .noRule := rfl
example : cvtU 32 64 10 = .error .noRule := rfl
-- A parameter pointer has no offset arithmetic (THREAD-POINTER-OFFSET).
example : (execLocal L 33 t (.int ⟨.add, .int .u 64, false, [some 30], [.reg 6, .imm 8]⟩)).map
    (·.regs 30) = .error .noRule := rfl
example : (execLocal L 33 t (.int ⟨.sub, .int .u 64, false, [some 30], [.reg 10, .imm 8]⟩)).map
    (·.regs 30) = .error .noRule := rfl
-- Generic accesses: the thread's own local memory, the constant memory; no store to it.
example : readAt (tmpl (load none (.reg 15 64) 4)) = some { loc := ⟨.local, 33, 20⟩, size := 4 } :=
  rfl
example : readAt (tmpl (load none (.reg 17 64))) = some { loc := ⟨.const, 0, 32⟩, size := 4 } :=
  rfl
example : ubOf (tmpl (load none (.reg 16 64))) = some .noRule := rfl
example : ubOf (tmpl { store with addr := ⟨.reg 17 64, 0⟩ }) = some .badValue := rfl
example : writeAt (tmpl { store with addr := ⟨.reg 15 64, 0⟩ }) =
    some ({ loc := ⟨.local, 33, 16⟩, size := 4 }, (Value.bits 32 12).toBytes) := rfl

/-! ## `.local` and `.const` variables (THREAD-ADDR, EXT-LOCAL-CONST-LAYOUT) -/

private def varEnv : Decode.Env := { env with locals := [("lv", 8)], consts := [("cv", 4)] }
private def ruleV (op : String) (args : List Syntax.Operand) : Except String (Option RuleId) :=
  Op.rule <$> Decode.op varEnv op args
private def S (s : String) (k : String) : Syntax.Operand :=
  .address [.offset "+" (.symbol s) (.literal k)]

example : ruleV "ld.local.u32" [R "%r0", .address [.symbol "lv"]] = .ok (some .threadAccess) :=
  rfl
example : ruleV "st.local.u32" [S "lv" "4", R "%r0"] = .ok (some .threadAccess) := rfl
example : ruleV "ld.const.u32" [R "%r0", S "cv" "4"] = .ok (some .threadAccess) := rfl
example : (Decode.op varEnv "ld.const.u32" [R "%r0", S "cv" "4"]).map
    (fun | .mem a => some a.addr | _ => none) = .ok (some ⟨.constSym 4, 4⟩) := rfl
-- A variable of another space has no rule.
example : ruleV "ld.global.u32" [R "%r0", .address [.symbol "lv"]] = .ok none := rfl
example : ruleV "ld.local.u32" [R "%r0", .address [.symbol "cv"]] = .ok none := rfl

private def L' : Launch := { L with localBase := 64, constBase := 128 }
example : readAt (memTmpl [] L' 33 t (load (some .local) (.localSym 8) 4)) =
    some { loc := ⟨.local, 33, 76⟩, size := 4 } := rfl
example : readAt (memTmpl [] L' 33 t (load (some .const) (.constSym 4))) =
    some { loc := ⟨.const, 0, 132⟩, size := 4 } := rfl

-- Moving a local symbol uses its offset from the launch's base.
example : Decode.op varEnv "mov.b64" [R "%rd0", .symbol "lv"] =
    .ok (.move ⟨.scalar, .int .b 64, [some 4], [.localSym 8]⟩) := rfl
example : (Decode.op varEnv "mov.b32" [R "%r0", .symbol "lv"]).isOk = false := rfl
example : (Decode.op varEnv "mov.b64" [R "%rd0", .symbol "missing"]).isOk = false := rfl
example : (Decode.op varEnv "mov.b64" [R "%rd0", .symbol "cv"]).isOk = false := rfl

private def movedLocal (g : Nat) : Exec Loc := do
  let u ← execLocal L' g t (.move ⟨.scalar, .int .b 64, [some 4], [.localSym 8]⟩)
  accessLoc L' g u (load (some .local) (.reg 4 64) 4)
example : movedLocal 33 = .ok ⟨.local, 33, 76⟩ := rfl
example : movedLocal 34 = .ok ⟨.local, 34, 76⟩ := rfl

-- The decoder lays the variables out; an initialized `.const` variable is rejected.
private def varSource : Syntax.Function := {
  name := "k"
  header := [".visible", ".entry", "k", "(", ")"]
  body := [.declaration [".local", ".align", "8", ".b8", "a", "[", "4", "]"],
    .declaration [".local", ".align", "8", ".b8", "b", "[", "8", "]"],
    .instruction none "ret" []] }
private def cDecl : List String := [".const", ".align", "4", ".b8", "c", "[", "16", "]"]
example : (Decode.prepare [cDecl] varSource).map (fun p => (p.env.locals, p.env.consts)) =
    .ok ([("a", 0), ("b", 8)], [("c", 0)]) := rfl
example : (Decode.prepare [cDecl ++ ["=", "{", "1", "}"]] varSource).isOk = false := rfl

/-! ## `[sym+imm]` of a `.shared` variable is the register form at the same address -/

example : rule "ld.shared.u32" [R "%r0", S "sh" "4"] = .ok (some .threadAccess) := rfl
example : rule "st.shared.u32" [S "sh" "4", R "%r0"] = .ok (some .threadAccess) := rfl
example : (Decode.op env "ld.shared.u32" [R "%r0", S "sh" "4"]).map
    (fun | .mem a => some a.addr | _ => none) = .ok (some ⟨.sharedSym 16, 4⟩) := rfl
example : readAt (tmpl (load (some (.shared .cta)) (.sharedSym 16) 4)) =
    readAt (tmpl (load (some (.shared .cta)) (.reg 11 32) 4)) := rfl
example : writeAt (tmpl (st (some (.shared .cta)) (.sharedSym 16) (.int .u 32) (.reg 12))) =
    writeAt (tmpl (st (some (.shared .cta)) (.reg 11 32) (.int .u 32) (.reg 12))) := rfl

/-! ## Prefetch and eviction priority (THREAD-PREFETCH) -/

example : execLocal L 33 t (.addr (.prefetch none false false ⟨.reg 1 64, 0⟩)) = .ok (next t) :=
  rfl
example : execLocal L 33 {} (.addr (.prefetch (some .local) true false ⟨.reg 1 64, 0⟩)) =
    .ok (next {}) := rfl
example : execLocal L 33 t (.addr (.applypriority true ⟨.reg 1 64, 128⟩)) = .ok (next t) := rfl
example : (execLocal L 33 t (.addr (.applypriority true ⟨.reg 8 64, 0⟩))).map (·.pc) =
    .error .misaligned := rfl
example : (execLocal L 33 t (.addr (.applypriority false ⟨.reg 1 64, 0⟩))).map (·.pc) =
    .error .noRule := rfl
example : (execLocal L 33 t (.addr (.prefetch none false true ⟨.reg 1 64, 0⟩))).map (·.pc) =
    .error .noRule := rfl

end
end PTX.Tests.MemWeak
