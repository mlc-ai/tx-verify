-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Assumption.IdealReal

/-!
# Vector `atom` and `red` (THREAD-ATOMIC)

The vector forms of §9.7.15.5 and §9.7.15.6 that have a rule, the events of a vector `atom`: one
atomic read-modify-write per scalar element at its adjacent location, reading register `e` of the
operand for vector element `e`, and the old values in the destination registers, and the rejected
cases.
-/

namespace PTX.Tests.AtomicVector
noncomputable section

/-! ## Rules of decoded forms -/

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 8, 32⟩, ⟨"%rd".toList, 4, 64⟩, ⟨"%rs".toList, 16, 16⟩,
      ⟨"%f".toList, 8, 32⟩],
    labels := [], params := [], shared := [("sh", 16)] }
private def R (s : String) : Syntax.Operand := .register s
private def A (s : String) : Syntax.Operand := .address [.register s]
private def names : String → List String
  | "%r" => ["%r0", "%r1", "%r2", "%r3", "%r4", "%r5", "%r6", "%r7"]
  | "%f" => ["%f0", "%f1", "%f2", "%f3", "%f4", "%f5", "%f6", "%f7"]
  | _ => ["%rs0", "%rs1", "%rs2", "%rs3", "%rs4", "%rs5", "%rs6", "%rs7", "%rs8", "%rs9",
      "%rs10", "%rs11", "%rs12", "%rs13", "%rs14", "%rs15"]
/-- The vector of registers `p i` to `p (i + n - 1)`. -/
private def V (p : String) (i n : Nat) : Syntax.Operand :=
  .vector (((names p).drop i).take n |>.map R)
private def rule (op : String) (args : List Syntax.Operand) : Option (Option RuleId) :=
  (Op.rule <$> Decode.op env op args).toOption

-- `.f32`: `add` of `.v2` and `.v4`, with and without `.noftz`, every `.sem` and `.scope` of `atom`,
-- the global space or a generic address.
example : ∀ sem ∈ ["", ".relaxed", ".acquire", ".release", ".acq_rel"],
    ∀ scope ∈ ["", ".cta", ".cluster", ".gpu", ".sys"],
    rule s!"atom{sem}{scope}.global.add.v2.f32" [V "%f" 0 2, A "%rd0", V "%f" 2 2] =
      some (some .threadAtomic) := by decide
example : rule "atom.global.add.noftz.v4.f32" [V "%f" 0 4, A "%rd0", V "%f" 4 4] =
    some (some .threadAtomic) := rfl
example : rule "atom.add.v4.f32" [V "%f" 0 4, A "%rd0", V "%f" 4 4] =
    some (some .threadAtomic) := rfl
example : rule "red.release.sys.global.add.v4.f32" [A "%rd0", V "%f" 0 4] =
    some (some .threadAtomic) := rfl
-- `.f16` and `.bf16`: `add`, `min` and `max` with `.noftz` of `.v2`, `.v4` and `.v8`.
example : ∀ op ∈ ["add", "min", "max"], ∀ ty ∈ ["f16", "bf16"],
    rule s!"atom.global.{op}.noftz.v8.{ty}" [V "%rs" 0 8, A "%rd0", V "%rs" 8 8] =
      some (some .threadAtomic) := by decide
example : rule "atom.global.max.noftz.v2.bf16" [V "%rs" 0 2, A "%rd0", V "%rs" 2 2] =
    some (some .threadAtomic) := rfl
example : rule "red.global.min.noftz.v4.f16" [A "%rd0", V "%rs" 0 4] =
    some (some .threadAtomic) := rfl
-- `.f16x2` and `.bf16x2`: `add`, `min` and `max` with `.noftz` of `.v2` and `.v4`.
example : ∀ op ∈ ["add", "min", "max"], ∀ ty ∈ ["f16x2", "bf16x2"],
    rule s!"atom.global.{op}.noftz.v4.{ty}" [V "%r" 0 4, A "%rd0", V "%r" 4 4] =
      some (some .threadAtomic) := by decide
example : rule "red.global.add.noftz.v2.bf16x2" [A "%rd0", V "%r" 0 2] =
    some (some .threadAtomic) := rfl
-- The sink destination and the cache policy.
example : rule "atom.global.add.noftz.v2.f16x2" [.sink, A "%rd0", V "%r" 0 2] =
    some (some .threadAtomic) := rfl
example : rule "atom.global.add.L2::cache_hint.v2.f32"
    [V "%f" 0 2, A "%rd0", V "%f" 2 2, R "%rd1"] = some (some .threadAtomic) := rfl

-- Rejected at decoding: a shared vector (vector `atom` "may be used only with .global space"),
-- `.v8` of `.f32` and of a packed type, `min` of `.f32`, a half type without `.noftz` and a
-- destination vector that mixes registers and the sink.
example : rule "atom.shared.add.v2.f32" [V "%f" 0 2, A "%rd0", V "%f" 2 2] = none := rfl
example : rule "red.shared::cluster.add.noftz.v2.f16" [A "%rd0", V "%rs" 0 2] = none := rfl
example : rule "atom.global.add.v8.f32" [V "%f" 0 8, A "%rd0", V "%f" 0 8] = none := rfl
example : rule "atom.global.min.v2.f32" [V "%f" 0 2, A "%rd0", V "%f" 2 2] = none := rfl
example : rule "atom.global.add.v2.f16" [V "%rs" 0 2, A "%rd0", V "%rs" 2 2] = none := rfl
example : rule "atom.global.add.noftz.v8.f16x2" [V "%r" 0 8, A "%rd0", V "%r" 0 8] = none :=
  rfl
example : rule "atom.global.add.v2.f32" [.vector [R "%f0", .sink], A "%rd0", V "%f" 2 2] = none :=
  rfl
-- Every vector form that decodes has a rule. An access the decoder never produces has none
-- (`atomicOk`): `.v8` of a packed type, a vector of the shared space, a mixed destination.
private def v2f32 : MemAccess :=
  { kind := .rmw .add, space := some .global, sem := .relaxed, elem := .float .f32, vec := 2,
    addr := ⟨.reg 8 64, 0⟩, dsts := [some 28, some 29], srcs := [.reg 30, .reg 31] }
example : v2f32.rule = some .threadAtomic := rfl
private def v8h2 : MemAccess :=
  { v2f32 with
    vec := 8, elem := .packed (.float .f16) 2, noftz := true,
    dsts := (List.range 8).map some, srcs := (List.range 8).map .reg }
example : v8h2.rule = none := rfl
example : { v2f32 with space := some (.shared .cta), addr := ⟨.reg 0 32, 0⟩ }.rule = none := rfl
example : { v2f32 with dsts := [some 28, none] }.rule = none := rfl

/-! ## Events -/

private def L : Launch := { grid := 2, block := 32, params := fun _ => none }
/-- `%rd0 = 16`, `%rd1 = 20`, `%rd2` a generic pointer to byte 16 of the CTA's shared memory,
`%r0 … %r3` packed pairs, `%f0 … %f3` single-precision values. -/
private def t : TState := { regs := fun
  | 8 => some (.bits 64 16)
  | 9 => some (.bits 64 20)
  | 10 => some (.ptr 64 true (.shared 0 0) 16)
  | 0 => some (.pair (.float .f16 1) (.float .f16 2))
  | 1 => some (.pair (.float .f16 3) (.float .f16 4))
  | 2 => some (.pair (.float .f16 5) (.float .f16 6))
  | 3 => some (.pair (.float .f16 7) (.float .f16 8))
  | 28 => some (.float .f32 1)
  | 29 => some (.float .f32 2)
  | 30 => some (.float .f32 3)
  | 31 => some (.float .f32 4)
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
private def next? (m : Tmpl) (old : List (Option Byte)) : Option TState :=
  match m with
  | .rmw _ _ k => some (k old)
  | _ => none
private def bytes (v : Value) : List (Option Byte) := v.toBytes.map some
private def at? (s : Nat) (u : TState := t) : TState := { u with sub := s }

-- `atom.global.add.noftz.v2.f16x2 {%r4, %r5}, [%rd0], {%r2, %r3}`: four 2-byte atomic
-- read-modify-writes at 16, 18, 20 and 22, elements 0 to 3 of one access.
private def addV2H2 : MemAccess :=
  mem "atom.global.add.noftz.v2.f16x2" [V "%r" 4 2, A "%rd0", V "%r" 2 2]
example : ∀ j ∈ [0, 1, 2, 3], acc? (memTmpl [] L 0 (at? j) addV2H2) =
    some { loc := ⟨.global, 0, 16 + 2 * j⟩, size := 2, elem := j, relaxed := true,
           scope := .gpu } := by
  intro j hj; simp only [List.mem_cons, List.not_mem_nil] at hj
  rcases hj with rfl | rfl | rfl | rfl | h <;> first | rfl | exact h.elim
-- Scalar element 3 is the high half of vector element 1, register `%r3`: its operand is `8`.
example : new? (memTmpl [] L 0 (at? 3) addV2H2) (bytes (.float .f16 0)) = some (do
    let v ← rmwValue [] .add (.float .f16) (← rebuild 3 (bytes (.float .f16 0))) [.float .f16 8]
    unless 8 * v.bytes = (DType.float .f16).width do throw .typeMismatch
    pure v.toBytes) := rfl
-- Scalar element 0 is the low half of vector element 0, register `%r2`: its operand is `5`.
example : new? (memTmpl [] L 0 (at? 0) addV2H2) (bytes (.float .f16 0)) = some (do
    let v ← rmwValue [] .add (.float .f16) (← rebuild 3 (bytes (.float .f16 0))) [.float .f16 5]
    unless 8 * v.bytes = (DType.float .f16).width do throw .typeMismatch
    pure v.toBytes) := rfl

/-- A whole value read back is that value (THREAD-BYTES). -/
private theorem rebuildWhole (v : Value) (n : Nat) (hn : v.bytes = n) (h2 : n = 2 ∨ n = 4)
    (hb : ∀ k, v.byteAt k = (v, k)) : rebuild 3 (bytes v) = .ok v := by
  rcases h2 with rfl | rfl <;> simp [bytes, rebuild, Value.toBytes, hn, List.range_succ, hb] <;> rfl

-- After the first three elements the old values are collected; the fourth writes `%r4` and `%r5`
-- with the packed old values of vector elements 0 and 1.
private def t3 : TState :=
  at? 3 { t with acc := [.float .f16 10, .float .f16 11, .float .f16 12] }
example : (next? (memTmpl [] L 0 t3 addV2H2) (bytes (.float .f16 13))).map
    (fun u => (u.regs 4, u.regs 5, u.pc, u.sub, u.acc)) =
    some (some (.pair (.float .f16 10) (.float .f16 11)),
      some (.pair (.float .f16 12) (.float .f16 13)), 1, 0, []) := by
  have h : next? (memTmpl [] L 0 t3 addV2H2) (bytes (.float .f16 13)) =
      some (afterAtom t3 [some 4, some 5] 2 4 (bytes (.float .f16 13))) := rfl
  rw [h, Option.map_some, afterAtom, rebuildWhole _ 2 rfl (.inl rfl) fun _ => rfl]
  simp [t3, at?, t, setRegs, setReg, pairUp]
-- An element before the last collects its old value.
example : (next? (memTmpl [] L 0 (at? 1) addV2H2) (bytes (.float .f16 13))).map
    (fun u => (u.sub, u.acc, u.pc)) = some (2, [.float .f16 13], 0) := by
  have h : next? (memTmpl [] L 0 (at? 1) addV2H2) (bytes (.float .f16 13)) =
      some (afterAtom (at? 1) [some 4, some 5] 2 4 (bytes (.float .f16 13))) := rfl
  rw [h, Option.map_some, afterAtom, rebuildWhole _ 2 rfl (.inl rfl) fun _ => rfl]
  simp [at?, t]

-- `red.global.add.v4.f32 [%rd0], {%f0, …, %f3}`: four 4-byte elements at 16 to 28, element `j`
-- taking `%fj`; the last element writes no register.
private def redV4 : MemAccess := mem "red.global.add.v4.f32" [A "%rd0", V "%f" 0 4]
example : ∀ j ∈ [0, 1, 2, 3], acc? (memTmpl [] L 0 (at? j) redV4) =
    some { loc := ⟨.global, 0, 16 + 4 * j⟩, size := 4, elem := j, relaxed := true,
           scope := .gpu } := by
  intro j hj; simp only [List.mem_cons, List.not_mem_nil] at hj
  rcases hj with rfl | rfl | rfl | rfl | h <;> first | rfl | exact h.elim
example : new? (memTmpl [] L 0 (at? 2) redV4) (bytes (.float .f32 0)) = some (do
    let v ← rmwValue [] .add (.float .f32) (← rebuild 3 (bytes (.float .f32 0))) [.float .f32 3]
    unless 8 * v.bytes = (DType.float .f32).width do throw .typeMismatch
    pure v.toBytes) := rfl
example : (next? (memTmpl [] L 0 (at? 3 { t with acc := [.float .f32 1, .float .f32 1,
    .float .f32 1] }) redV4) (bytes (.float .f32 1))).map (fun u => (u.regs 28, u.pc)) =
    some (some (.float .f32 1), 1) := by
  have h : next? (memTmpl [] L 0 (at? 3 { t with acc := [.float .f32 1, .float .f32 1,
      .float .f32 1] }) redV4) (bytes (.float .f32 1)) =
      some (afterAtom (at? 3 { t with acc := [.float .f32 1, .float .f32 1, .float .f32 1] }) []
        1 4 (bytes (.float .f32 1))) := rfl
  rw [h, Option.map_some, afterAtom, rebuildWhole _ 4 rfl (.inr rfl) fun _ => rfl]
  simp [at?, t]
-- With an ideal-real assumption the half-precision `max` of a vector form has a value.
private def ideal : Assumption :=
  Assumption.idealReal "atomic-max" { rmw := [(.max, .float .f16)] } "test"
example : rmwValue [ideal] .max (.float .f16) (.float .f16 1) [.float .f16 2] =
    .ok (.float .f16 2) := by
  simp [rmwValue, ideal, Assumption.idealReal, Assumption.idealRmw, valFloat]; rfl

-- Rejected events: a generic address of a shared location (vector `atom` "may be used only with
-- .global space and with generic addressing where the address points to .global space"), where
-- the scalar form has an event, and an address that is not a multiple of the 8-byte access size.
example : memTmpl [] L 0 t (mem "atom.add.v2.f32" [V "%f" 0 2, A "%rd2", V "%f" 2 2]) =
    .ub .noRule := rfl
example : acc? (memTmpl [] L 0 t (mem "atom.add.f32" [R "%f0", A "%rd2", R "%f2"])) =
    some { loc := ⟨.shared, 0, 16⟩, size := 4, relaxed := true, scope := .gpu } := rfl
example : memTmpl [] L 0 t (mem "atom.global.add.v2.f32" [V "%f" 0 2, A "%rd1", V "%f" 2 2]) =
    .ub .misaligned := rfl
example : memTmpl [] L 0 (at? 1) (mem "red.global.add.noftz.v4.f16" [A "%rd1", V "%rs" 0 4]) =
    .ub .misaligned := rfl
-- A form without a rule has no event.
example : memTmpl [] L 0 t { v2f32 with dsts := [some 28, none] } = .ub .noRule := rfl

end
end PTX.Tests.AtomicVector
