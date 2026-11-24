-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Thread.Local
public import Kernels.Fp16Gemm8192.Ptx

namespace PTX.Tests.ParameterObjects

-- The production by-value tensor maps retain their storage, not three pointer values.
example : Decode.parameterDecls Generated.Fp16Gemm8192.gemm_kernel.header =
    .ok ([], [], [⟨"gemm_kernel_param_0", 8, 128, 128⟩,
      ⟨"gemm_kernel_param_1", 8, 128, 128⟩,
      ⟨"gemm_kernel_param_2", 8, 128, 128⟩]) := rfl

example : Decode.parameterDecls ["(", ".param", ".u64", "p", ",",
    ".param", ".align", "16", ".b8", "buffer", "[", "64", "]", ")"] =
    .ok ([("p", 64)], [], [⟨"buffer", 8, 64, 16⟩]) := rfl

example : Decode.paramObject [".param", ".b32", "values", "[", "4", "]"] =
    .ok ⟨"values", 32, 4, 4⟩ := rfl
example : (ParamObjectDecl.mk "values" 32 4 4).bytes = 16 := rfl
example : Decode.paramObject [".param", ".align", "3", ".b8", "a", "[", "16", "]"] =
    .error "parameter alignment is not a power of two" := rfl
example : Decode.paramObject [".param", ".align", "16", ".b8", "a", "[", "0", "]"] =
    .error "zero parameter array extent" := rfl

-- Object declarations survive whole-function decoding even if the object is unused.
private def source : Syntax.Function := {
  name := "parameter_object"
  header := [".visible", ".entry", "parameter_object", "(", ".param", ".align", "16",
    ".b8", "a", "[", "64", "]", ")"]
  body := [.instruction none "ret" []] }
example : Decode.kernel source = .ok {
    name := "parameter_object", params := [], paramObjects := [⟨"a", 8, 64, 16⟩],
    code := [⟨none, .ret⟩] } := rfl

-- Unused module globals are not shared allocations or parameter values.
example : Decode.kernelIn [[".global", ".align", "1", ".b8", "unused", "[", "1", "]"]] source =
    Decode.kernel source := rfl

-- A global symbol must not accidentally become a shared or scalar parameter address.
example : Decode.kernelIn [[".global", ".align", "1", ".b8", "unused", "[", "1", "]"]]
    { source with body := [.declaration [".reg", ".b64", "%rd", "<", "1", ">"],
      .instruction none "mov.b64" [.register "%rd0", .symbol "unused"],
      .instruction none "ret" []] } = .error "unknown symbol unused" := rfl

/-! ## `ld.param` on a by-value parameter object (PROG-DECODE, THREAD-MOVE)

FA4 reads 32-bit words and a `.v2.b8` pair of `.param .align 4 .b8 obj[12]` into `.b32` and
`.b16` registers. -/

private def obj : ParamObjectDecl := ⟨"obj", 8, 12, 4⟩
private def objEnv : Decode.Env :=
  { classes := [⟨"%r".toList, 2, 32⟩, ⟨"%rd".toList, 1, 64⟩, ⟨"%rs".toList, 2, 16⟩,
      ⟨"%c".toList, 1, 8⟩],
    labels := [], params := [("s32", 32), ("obj", 96), ("odd", 64), ("big", 256)],
    objects := [obj, ⟨"odd", 8, 8, 2⟩, ⟨"big", 8, 32, 32⟩] }
private def objAt (p : String) (k : String) : Syntax.Operand :=
  .address [.offset "+" (.symbol p) (.literal k)]

example : Decode.op objEnv "ld.param.b32" [.register "%r0", .address [.symbol "obj"]] =
    .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
      addr := ⟨.param "obj" true, 0⟩, dsts := [some 0] }) := rfl
example : Decode.op objEnv "ld.param.b32" [.register "%r1", objAt "obj" "4"] =
    .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
      addr := ⟨.param "obj" true, 4⟩, dsts := [some 1] }) := rfl
example : Decode.op objEnv "ld.param.v2.b8" [.vector [.register "%rs0", .register "%rs1"],
    objAt "obj" "8"] = .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 8, vec := 2,
      ext := .zero 16,
      addr := ⟨.param "obj" true, 8⟩, dsts := [some 3, some 4] }) := rfl
-- A bit-size type may load into a wider register (zero-extended, §9.4.1 Table 28).
example : Decode.op objEnv "ld.param.b32" [.register "%rd0", objAt "obj" "8"] =
    .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 32, ext := .zero 64,
      addr := ⟨.param "obj" true, 8⟩, dsts := [some 2] }) := rfl
-- A scalar parameter keeps its own form.
example : Decode.op objEnv "ld.param.b32" [.register "%r0", .address [.symbol "s32"]] =
    .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
      addr := ⟨.param "s32" false, 0⟩, dsts := [some 0] }) := rfl
example : MemAccess.rule {
    kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
    addr := ⟨.param "s32" false, 0⟩, dsts := [some 0] } = some .threadMove := rfl
-- A scalar parameter into a wider register decodes with `MemExt.zero` and is zero-extended
-- (THREAD-MOVE, §9.7.10.8).
example : Decode.op objEnv "ld.param.b32" [.register "%rd0", .address [.symbol "s32"]] =
    .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 32, ext := .zero 64,
      addr := ⟨.param "s32" false, 0⟩, dsts := [some 2] }) := rfl
example : MemAccess.rule {
    kind := .load, space := some .param, sem := .weak, elem := .int .b 32, ext := .zero 64,
    addr := ⟨.param "s32" false, 0⟩, dsts := [some 2] } = some .threadMove := rfl

-- Rejected: beyond the object, a negative offset, an offset or a declared alignment the access
-- size does not divide, unequal destination widths, a `.b128` element in a 64-bit register,
-- `.v4.b64` outside the global space, an offset on a scalar parameter, a repeated destination
-- register.
example : (Decode.op objEnv "ld.param.b32" [.register "%r0", objAt "obj" "12"]).isOk = false := rfl
example : (Decode.op objEnv "ld.param.b32" [.register "%r0", objAt "obj" "-4"]).isOk = false := rfl
example : (Decode.op objEnv "ld.param.b32" [.register "%r0", objAt "obj" "2"]).isOk = false := rfl
example : (Decode.op objEnv "ld.param.b32" [.register "%r0", objAt "odd" "4"]).isOk = false := rfl
example : Decode.op objEnv "ld.param.b16" [.register "%rs0", objAt "odd" "4"] =
    .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 16,
      addr := ⟨.param "odd" true, 4⟩, dsts := [some 3] }) := rfl
-- A signed type into a wider register is sign-extended (`MemExt.sign`, THREAD-MOVE).
example : Decode.op objEnv "ld.param.s8" [.register "%rs0", objAt "obj" "8"] =
    .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .s 8, ext := .sign 16,
      addr := ⟨.param "obj" true, 8⟩, dsts := [some 3] }) := rfl
example : MemAccess.rule {
    kind := .load, space := some .param, sem := .weak, elem := .int .s 8, ext := .sign 16,
    addr := ⟨.param "obj" true, 8⟩, dsts := [some 3] } = some .threadMove := rfl
example : Decode.op objEnv "ld.param.s8" [.register "%c0", objAt "obj" "8"] =
    .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .s 8,
      addr := ⟨.param "obj" true, 8⟩, dsts := [some 5] }) := rfl
example : (Decode.op objEnv "ld.param.v2.b8" [.vector [.register "%rs0", .register "%r0"],
    objAt "obj" "8"]).isOk = false := rfl
example : (Decode.op objEnv "ld.param.b128" [.register "%rd0", .address [.symbol "big"]]).isOk =
    false := rfl
example : (Decode.op objEnv "ld.param.v4.b64" [.vector [.register "%rd0", .register "%rd0",
    .register "%rd0", .register "%rd0"], .address [.symbol "big"]]).isOk = false := rfl
example : (Decode.op objEnv "ld.param.b32" [.register "%r0", objAt "s32" "4"]).isOk = false := rfl
-- A zero offset names the parameter itself.
example : Decode.op objEnv "ld.param.b32" [.register "%r0", objAt "s32" "0"] =
    Decode.op objEnv "ld.param.b32" [.register "%r0", .address [.symbol "s32"]] := rfl
example : (Decode.op objEnv "ld.param.v2.b8" [.vector [.register "%rs0", .register "%rs0"],
    objAt "obj" "8"]).isOk = false := rfl

-- Execution: bytes `4 … 7` little-endian (EXT-ENDIAN), then bytes 8 and 9 zero-extended into
-- 16-bit registers, element `j` at byte `8 + j` (EXT-VECTOR-ELEM).
private def objBytes (p : String) (k : Nat) : Option (BitVec 8) :=
  if p = "obj" ∧ k < 12 then some (BitVec.ofNat 8 (k + 1)) else none
private def L : Launch :=
  { grid := 1, block := 1, params := fun _ => none, paramBytes := objBytes }

example : ((execMove L 0 {} (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
      addr := ⟨.param "obj" true, 4⟩, dsts := [some 0] })).map (·.regs 0)) =
    .ok (some (.bits 32 0x08070605)) := by rfl
example : ((execMove L 0 {} (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 8, vec := 2,
      ext := .zero 16,
      addr := ⟨.param "obj" true, 8⟩, dsts := [some 3, some 4] })).map
    (fun t => (t.regs 3, t.regs 4, t.pc))) = .ok (some (.bits 16 9), some (.bits 16 10), 1) := by
  rfl
-- A byte the launch does not supply faults.
example : ((execMove L 0 {} (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
      addr := ⟨.param "other" true, 0⟩, dsts := [some 0] })).map (·.pc)) =
    .error .badParam := by rfl

end PTX.Tests.ParameterObjects
