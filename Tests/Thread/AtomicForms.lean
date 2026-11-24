-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Assumption.IdealReal

/-!
# `atom` and `red`: forms, operations and templates (THREAD-ATOMIC, THREAD-ATOMIC-OP)

Which forms have a rule, the value of every operation at its boundary values (the Semantics of
§9.7.15.5), the event an `atom` or `red` performs with its semantics and scope, the floating forms
with and without an assumption, and the rejected cases.
-/

namespace PTX.Tests.AtomicForms
noncomputable section

/-! ## Rules of decoded forms -/

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 4, 64⟩, ⟨"%rs".toList, 4, 16⟩,
      ⟨"%q".toList, 4, 128⟩, ⟨"%f".toList, 4, 32⟩, ⟨"%fd".toList, 4, 64⟩],
    labels := [], params := [], shared := [("sh", 16)] }
private def R (s : String) : Syntax.Operand := .register s
private def A (s : String) : Syntax.Operand := .address [.register s]
private def I (s : String) : Syntax.Operand := .literal s
private def rule (op : String) (args : List Syntax.Operand) : Option (Option RuleId) :=
  (Op.rule <$> Decode.op env op args).toOption

-- Every `.sem`, every `.scope` and every state space of an integer `atom`, and the defaults.
example : rule "atom.global.add.u32" [R "%r0", A "%rd0", R "%r1"] = some (some .threadAtomic) :=
  rfl
example : ∀ sem ∈ ["", ".relaxed", ".acquire", ".release", ".acq_rel"],
    ∀ scope ∈ ["", ".cta", ".cluster", ".gpu", ".sys"],
    rule s!"atom{sem}{scope}.global.add.u32" [R "%r0", A "%rd0", R "%r1"] =
      some (some .threadAtomic) := by decide
example : ∀ space ∈ [".global", ".shared", ".shared::cta", ".shared::cluster", ""],
    rule s!"atom{space}.inc.u32" [R "%r0", A "%rd0", R "%r1"] = some (some .threadAtomic) := by
  decide
example : rule "atom.shared.max.s32" [R "%r0", .address [.symbol "sh"], I "3"] =
    some (some .threadAtomic) := rfl
-- Table 41: the integer and bit operations of each type.
example : ∀ op ∈ ["add", "inc", "dec", "min", "max"],
    rule s!"atom.global.{op}.u32" [R "%r0", A "%rd0", R "%r1"] = some (some .threadAtomic) := by
  decide
example : ∀ ty ∈ ["s32", "u64"], ∀ op ∈ ["add", "min", "max"],
    rule s!"atom.global.{op}.{ty}" [R (if ty = "s32" then "%r0" else "%rd0"), A "%rd1",
      R (if ty = "s32" then "%r1" else "%rd2")] = some (some .threadAtomic) := by decide
example : ∀ op ∈ ["min", "max"],
    rule s!"atom.global.{op}.s64" [R "%rd0", A "%rd1", R "%rd2"] = some (some .threadAtomic) := by
  decide
example : ∀ op ∈ ["and", "or", "xor", "exch"],
    rule s!"atom.global.{op}.b32" [R "%r0", A "%rd0", R "%r1"] = some (some .threadAtomic) := by
  decide
example : ∀ op ∈ ["and", "or", "xor", "exch"],
    rule s!"atom.global.{op}.b64" [R "%rd0", A "%rd1", R "%rd2"] = some (some .threadAtomic) := by
  decide
example : rule "atom.global.exch.b128" [R "%q0", A "%rd0", R "%q1"] = some (some .threadAtomic) :=
  rfl
example : rule "atom.global.cas.b16" [R "%rs0", A "%rd0", R "%rs1", R "%rs2"] =
    some (some .threadAtomic) := rfl
example : rule "atom.global.cas.b32" [R "%r0", A "%rd0", R "%r1", R "%r2"] =
    some (some .threadAtomic) := rfl
example : rule "atom.global.cas.b64" [R "%rd0", A "%rd1", R "%rd2", R "%rd3"] =
    some (some .threadAtomic) := rfl
example : rule "atom.shared.cas.b128" [R "%q0", A "%r0", R "%q1", R "%q2"] =
    some (some .threadAtomic) := rfl
-- The floating `add` forms (the value is an assumption's) and the sink destination.
example : rule "atom.global.add.f32" [R "%f0", A "%rd0", R "%f1"] = some (some .threadAtomic) :=
  rfl
example : rule "atom.global.add.noftz.f32" [R "%f0", A "%rd0", R "%f1"] =
    some (some .threadAtomic) := rfl
example : rule "atom.global.add.f64" [R "%fd0", A "%rd0", R "%fd1"] = some (some .threadAtomic) :=
  rfl
example : rule "atom.global.add.noftz.f16" [R "%rs0", A "%rd0", R "%rs1"] =
    some (some .threadAtomic) := rfl
example : rule "atom.global.add.noftz.bf16x2" [R "%r0", A "%rd0", R "%r1"] =
    some (some .threadAtomic) := rfl
example : rule "atom.global.add.u32" [.sink, A "%rd0", R "%r1"] = some (some .threadAtomic) := rfl
example : rule "atom.global.cas.b32" [.sink, A "%rd0", R "%r1", R "%r2"] =
    some (some .threadAtomic) := rfl
example : rule "atom.global.add.L2::cache_hint.u32" [R "%r0", A "%rd0", R "%r1", R "%rd1"] =
    some (some .threadAtomic) := rfl
-- `red`: Table 42, `.relaxed` and `.release`, every scope and space.
example : ∀ sem ∈ ["", ".relaxed", ".release"], ∀ scope ∈ ["", ".cta", ".cluster", ".gpu", ".sys"],
    rule s!"red{sem}{scope}.global.add.u32" [A "%rd0", R "%r1"] = some (some .threadAtomic) := by
  decide
example : ∀ space ∈ [".global", ".shared", ".shared::cta", ".shared::cluster", ""],
    rule s!"red{space}.min.s32" [A "%rd0", R "%r1"] = some (some .threadAtomic) := by decide
example : ∀ op ∈ ["and", "or", "xor"],
    rule s!"red.global.{op}.b64" [A "%rd0", R "%rd1"] = some (some .threadAtomic) := by decide
example : rule "red.global.add.f32" [A "%rd0", R "%f1"] = some (some .threadAtomic) := rfl
example : rule "red.global.add.noftz.f16x2" [A "%rd0", R "%r1"] = some (some .threadAtomic) := rfl

-- Rejected at decoding: combinations Table 41 does not list. Vector forms have a rule
-- (Tests/Thread/AtomicVector.lean).
example : rule "atom.global.inc.s32" [R "%r0", A "%rd0", R "%r1"] = none := rfl
example : rule "atom.global.add.s64" [R "%rd0", A "%rd1", R "%rd2"] = none := rfl
example : rule "atom.global.and.u32" [R "%r0", A "%rd0", R "%r1"] = none := rfl
example : rule "atom.global.add.v2.f32" [.vector [R "%f0", R "%f1"], A "%rd0",
    .vector [R "%f2", R "%f3"]] = some (some .threadAtomic) := rfl
example : rule "red.global.add.v4.f32" [A "%rd0", .vector [R "%f0", R "%f1", R "%f2", R "%f3"]] =
    some (some .threadAtomic) := rfl
-- Rejected at decoding: `red` has no `.acquire`, `.cas` or `.exch`, `atom` no local space and no
-- floating `min` of a scalar.
example : rule "red.acquire.global.add.u32" [A "%rd0", R "%r1"] = none := rfl
example : rule "red.global.cas.b32" [A "%rd0", R "%r1", R "%r2"] = none := rfl
example : rule "atom.local.add.u32" [R "%r0", A "%rd0", R "%r1"] = none := rfl
example : rule "atom.global.min.f32" [R "%f0", A "%rd0", R "%f1"] = none := rfl

/-! ## The values of the operations (THREAD-ATOMIC-OP) -/

-- inc and dec: "inc(r, s) = (r >= s) ? 0 : r+1; dec(r, s) = (r==0 || r > s) ? s : r-1;"
example : AtomOp.apply .inc false 32 5 5 = 0 ∧ AtomOp.apply .inc false 32 4 5 = 5 ∧
    AtomOp.apply .inc false 32 7 5 = 0 := by decide
example : AtomOp.apply .dec false 32 0 5 = 5 ∧ AtomOp.apply .dec false 32 6 5 = 5 ∧
    AtomOp.apply .dec false 32 5 5 = 4 := by decide
-- add wraps at the width; min and max compare as signed for `.s` types.
example : AtomOp.apply .add false 32 0xffffffff 2 = 1 := by decide
example : AtomOp.apply .min true 32 0xffffffff 1 = 0xffffffff ∧
    AtomOp.apply .min false 32 0xffffffff 1 = 1 := by decide
example : AtomOp.apply .max true 64 (2 ^ 63) 0 = 0 ∧
    AtomOp.apply .max false 64 (2 ^ 63) 0 = 2 ^ 63 :=
  by decide
example : AtomOp.apply .and false 32 0xf0 0x3c = 0x30 ∧ AtomOp.apply .or false 32 0xf0 0x3c = 0xfc ∧
    AtomOp.apply .xor false 32 0xf0 0x3c = 0xcc ∧ AtomOp.apply .exch false 32 0xf0 0x3c = 0x3c := by
  decide
-- cas: "cas(r,s,t) = (r == s) ? t : r", on bit patterns, 128 bits as two halves.
example : rmwValue [] .cas (.int .b 32) (.bits 32 5) [.bits 32 5, .bits 32 9] = .ok (.bits 32 9) :=
  rfl
example : rmwValue [] .cas (.int .b 32) (.bits 32 5) [.bits 32 6, .bits 32 9] = .ok (.bits 32 5) :=
  rfl
example : rmwValue [] .cas (.int .b 16) (.bits 16 7) [.bits 16 7, .bits 16 1] = .ok (.bits 16 1) :=
  rfl
example : rmwValue [] .exch (.int .b 128) (.pair (.bits 64 1) (.bits 64 2))
    [.pair (.bits 64 3) (.bits 64 4)] = .ok (.pair (.bits 64 3) (.bits 64 4)) := by
  simp [rmwValue, Value.bitPattern, Value.bytes, Value.ofWidth, AtomOp.apply]; rfl
-- An operand of another size is `typeMismatch`.
example : rmwValue [] .add (.int .u 32) (.bits 32 5) [.bits 64 1] = .error .typeMismatch := rfl
-- A floating operation has no Core rule.
example : rmwValue [] .add (.float .f32) (.float .f32 1) [.float .f32 2] = .error .noRule := rfl
-- Under an ideal-real assumption that names it, `add.f32` is the exact sum; `.f64` stays without
-- a value.
private def ideal : Assumption :=
  Assumption.idealReal "atomic-add" { rmw := [(.add, .float .f32), (.add, .float .f64)] } "test"
example : rmwValue [ideal] .add (.float .f32) (.float .f32 1) [.float .f32 2] =
    .ok (.float .f32 3) := by
  simp [rmwValue, ideal, Assumption.idealReal, Assumption.idealRmw, valFloat]; norm_num; rfl
example : rmwValue [ideal] .add (.float .f64) (.float .f32 1) [.float .f32 2] = .error .noRule := by
  simp [rmwValue, ideal, Assumption.idealReal, Assumption.idealRmw]

/-! ## Events (THREAD-ATOMIC) -/

private def L : Launch := { grid := 2, block := 32, params := fun _ => none }
private def t : TState := { regs := fun
  | 4 => some (.bits 64 16)
  | 5 => some (.bits 64 18)
  | 1 => some (.bits 32 7)
  | 2 => some (.bits 32 9)
  | _ => none }
private def mem (op : String) (args : List Syntax.Operand) : MemAccess :=
  match Decode.op env op args with
  | .ok (.mem a) => a
  | _ => { kind := .load, space := none, sem := .weak, elem := .pred, addr := ⟨.imm 0, 0⟩ }
private def acc? : Tmpl → Option Acc
  | .rmw a _ _ => some a
  | _ => none
private def new? (m : Tmpl) (old : List (Option Byte)) : Option (Exec (List Byte)) :=
  match m with
  | .rmw _ f _ => some (f old)
  | _ => none
private def reg? (m : Tmpl) (old : List (Option Byte)) (r : Nat) : Option (Option Value) :=
  match m with
  | .rmw _ _ k => some ((k old).regs r)
  | _ => none
private def bytes (v : Value) : List (Option Byte) := v.toBytes.map some

-- `atom.global.add.u32 %r0, [%rd0], %r1`: one strong `.relaxed.gpu` 4-byte read-modify-write at
-- global address 16; it writes `old + 7` and returns the old value in `%r0`.
private def addU32 : MemAccess := mem "atom.global.add.u32" [R "%r0", A "%rd0", R "%r1"]
example : acc? (memTmpl [] L 0 t addU32) =
    some { loc := ⟨.global, 0, 16⟩, size := 4, relaxed := true, scope := .gpu } := rfl
/-- A whole 4-byte value read back is that value (THREAD-BYTES). -/
private theorem rebuild4 (v : Value) (h4 : v.bytes = 4) (hb : ∀ k, v.byteAt k = (v, k)) :
    rebuild 3 (bytes v) = .ok v := by
  simp [bytes, rebuild, Value.toBytes, h4, List.range_succ, hb]; rfl
/-- The write of an integer `atom` element at THREAD-ATOMIC-OP's value. -/
private theorem writes (A : List Assumption) (op : AtomOp) (ty : DType) (old : Value)
    (srcs : List Value) (h4 : old.bytes = 4) (hb : ∀ k, old.byteAt k = (old, k)) :
    (do
      let v ← rmwValue A op ty (← rebuild 3 (bytes old)) srcs
      unless 8 * v.bytes = ty.width do throw .typeMismatch
      pure v.toBytes : Exec (List Byte)) =
    (do
      let v ← rmwValue A op ty old srcs
      unless 8 * v.bytes = ty.width do throw .typeMismatch
      pure v.toBytes) := by
  rw [rebuild4 old h4 hb]; rfl
example : new? (memTmpl [] L 0 t addU32) (bytes (.bits 32 5)) =
    some (.ok (Value.bits 32 12).toBytes) := by
  have h : new? (memTmpl [] L 0 t addU32) (bytes (.bits 32 5)) = some (do
      let v ← rmwValue [] .add (.int .u 32) (← rebuild 3 (bytes (.bits 32 5))) [.bits 32 7]
      unless 8 * v.bytes = (DType.int .u 32).width do throw .typeMismatch
      pure v.toBytes) := rfl
  rw [h, writes _ _ _ _ _ rfl fun _ => rfl]; rfl
example : reg? (memTmpl [] L 0 t addU32) (bytes (.bits 32 5)) 0 = some (some (.bits 32 5)) := by
  have h : reg? (memTmpl [] L 0 t addU32) (bytes (.bits 32 5)) 0 =
      some ((afterAtom t [some 0] 1 1 (bytes (.bits 32 5))).regs 0) := rfl
  rw [h, afterAtom, rebuild4 (.bits 32 5) rfl fun _ => rfl]
  simp [setRegs, setReg, t]
-- `.acq_rel.cluster` acquires and releases at cluster scope; `red.release` releases only.
example : acc? (memTmpl [] L 0 t (mem "atom.acq_rel.cluster.global.exch.b32"
    [R "%r0", A "%rd0", R "%r1"])) =
    some { loc := ⟨.global, 0, 16⟩, size := 4, acquire := true, release := true,
           scope := .cluster } :=
  rfl
example : acc? (memTmpl [] L 0 t (mem "red.release.sys.global.add.u32" [A "%rd0", R "%r1"])) =
    some { loc := ⟨.global, 0, 16⟩, size := 4, release := true, scope := .sys } := rfl
-- `cas` writes the swap operand when the old value equals the compare operand.
private def casB32 : MemAccess := mem "atom.global.cas.b32" [R "%r0", A "%rd0", R "%r1", R "%r2"]
example : new? (memTmpl [] L 0 t casB32) (bytes (.bits 32 7)) =
    some (.ok (Value.bits 32 9).toBytes) := by
  have h : new? (memTmpl [] L 0 t casB32) (bytes (.bits 32 7)) = some (do
      let v ← rmwValue [] .cas (.int .b 32) (← rebuild 3 (bytes (.bits 32 7)))
        [.bits 32 7, .bits 32 9]
      unless 8 * v.bytes = (DType.int .b 32).width do throw .typeMismatch
      pure v.toBytes) := rfl
  rw [h, writes _ _ _ _ _ rfl fun _ => rfl]; rfl
example : new? (memTmpl [] L 0 t casB32) (bytes (.bits 32 8)) =
    some (.ok (Value.bits 32 8).toBytes) := by
  have h : new? (memTmpl [] L 0 t casB32) (bytes (.bits 32 8)) = some (do
      let v ← rmwValue [] .cas (.int .b 32) (← rebuild 3 (bytes (.bits 32 8)))
        [.bits 32 7, .bits 32 9]
      unless 8 * v.bytes = (DType.int .b 32).width do throw .typeMismatch
      pure v.toBytes) := rfl
  rw [h, writes _ _ _ _ _ rfl fun _ => rfl]; rfl
-- A floating `atom` without an assumption: its write has no value (`noRule`).
private def addF32 : MemAccess := mem "atom.global.add.f32" [R "%f0", A "%rd0", R "%f1"]
private def tF : TState :=
  { t with regs := fun r => if r = 17 then some (.float .f32 2) else t.regs r }
example : new? (memTmpl [] L 0 tF addF32) (bytes (.float .f32 1)) = some (.error .noRule) := by
  have h : new? (memTmpl [] L 0 tF addF32) (bytes (.float .f32 1)) = some (do
      let v ← rmwValue [] .add (.float .f32) (← rebuild 3 (bytes (.float .f32 1)))
        [.float .f32 2]
      unless 8 * v.bytes = (DType.float .f32).width do throw .typeMismatch
      pure v.toBytes) := rfl
  rw [h, writes _ _ _ _ _ rfl fun _ => rfl]; rfl
-- The event of such a write records no bytes, and the thread's next event is `ub noRule`.
example (o : List (Option Byte)) (f : List (Option Byte) → Exec (List Byte))
    (k : List (Option Byte) → TState) (a : Acc) (h : f o = .error .noRule)
    (hl : o.length = a.size) :
    Fires 3 (.rmw a f k) ⟨3, .rmw a o none⟩ (some { k o with fault := some .noRule }) :=
  ⟨o, hl, by rw [h]; rfl, by rw [h]⟩
-- `.f16x2`: two 2-byte elements, each its own atomic operation, the second at offset 2.
private def addH2 : MemAccess := mem "atom.global.add.noftz.f16x2" [R "%r0", A "%rd0", R "%r1"]
private def tH : TState :=
  { t with
    regs := fun r => if r = 1 then some (.pair (.float .f16 1) (.float .f16 2)) else t.regs r }
example : acc? (memTmpl [] L 0 tH addH2) =
    some { loc := ⟨.global, 0, 16⟩, size := 2, relaxed := true, scope := .gpu } := rfl
example : acc? (memTmpl [] L 0 { tH with sub := 1 } addH2) =
    some { loc := ⟨.global, 0, 18⟩, size := 2, relaxed := true, scope := .gpu, elem := 1 } := rfl
-- Misaligned: a 4-byte `atom` at address 18.
example : memTmpl [] L 0 t (mem "atom.global.add.u32" [R "%r0", A "%rd1", R "%r1"]) =
    .ub .misaligned := rfl

end
end PTX.Tests.AtomicForms
