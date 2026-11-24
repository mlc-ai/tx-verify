-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
import all Init.Data.ToString.Extra
import all Init.Data.Repr

namespace PTX.Tests.Scopes
open PTX.Syntax

def source : Function where
  name := "scopes"
  header := [".visible", ".entry", "scopes", "(", ")"]
  body := [
    .declaration [".reg", ".b32", "%r", "<", "2", ">"],
    .scope [.declaration [".reg", ".b32", "tmp"],
      .instruction none "mov.b32" [.symbol "tmp", .literal "7"],
      .instruction none "mov.b32" [.register "%r0", .symbol "tmp"]],
    .scope [.declaration [".reg", ".b32", "tmp"],
      .instruction none "mov.b32" [.symbol "tmp", .literal "9"],
      .instruction none "mov.b32" [.register "%r1", .symbol "tmp"]],
    .instruction none "ret" []]

-- Scalar registers without '%' and sibling scopes resolve to distinct identities.
example : Decode.kernel source = .ok {
    name := "scopes", params := [], regNames := ["%r0", "%r1", "#/1#tmp", "#/2#tmp"], code := [
      ⟨none, .move ⟨.scalar, .int .b 32, [some 2], [.imm 7]⟩⟩,
      ⟨none, .move ⟨.scalar, .int .b 32, [some 0], [.reg 2]⟩⟩,
      ⟨none, .move ⟨.scalar, .int .b 32, [some 3], [.imm 9]⟩⟩,
      ⟨none, .move ⟨.scalar, .int .b 32, [some 1], [.reg 3]⟩⟩,
      ⟨none, .ret⟩]} := by rfl

def shadow : List Statement := [
  .declaration [".reg", ".pred", "p"],
  .scope [.declaration [".reg", ".pred", "p"],
    .instruction (some ("p", false)) "bra" [.symbol "done"],
    .label "done"],
  .instruction (some ("p", false)) "bra" [.symbol "done"],
  .label "done"]

-- A nested predicate and label shadow the parent only inside that scope.
example : Decode.resolveScopes (Decode.scopeDepth shadow) shadow [] "" = .ok [
    .declaration [".reg", ".pred", "p"],
    .declaration [".reg", ".pred", "#/1#p"],
    .instruction (some ("#/1#p", false)) "bra" [.symbol "#/1#done"],
    .label "#/1#done",
    .instruction (some ("p", false)) "bra" [.symbol "done"],
    .label "done"] := by rfl

-- A scalar register cannot be mistaken for a numbered family.
example : Decode.regWidth [⟨"p".toList, 0, 1⟩] "p" = .ok 1 := by rfl
example : Decode.regWidth [⟨"p".toList, 0, 1⟩] "p0" =
    .error "undeclared or ambiguous register p0" := by rfl

/-! `.shared` variables are scoped like registers (§9.7.14.1, "any variable declared within a
scope is not available outside the scope"); ptxas 13.2 accepts both programs below. -/

def sharedSiblings : Function where
  name := "siblings"
  header := [".visible", ".entry", "siblings", "(", ")"]
  body := [
    .declaration [".reg", ".b32", "%r", "<", "2", ">"],
    .scope [.declaration [".shared", ".align", "4", ".b8", "buf", "[", "4", "]"],
      .instruction none "mov.u32" [.register "%r0", .symbol "buf"]],
    .scope [.declaration [".shared", ".align", "4", ".b8", "buf", "[", "4", "]"],
      .instruction none "mov.u32" [.register "%r1", .symbol "buf"]],
    .instruction none "ret" []]

-- Sibling blocks' `buf` are two variables at disjoint offsets.
example : (Decode.kernel sharedSiblings).map (·.code) = .ok [
    ⟨none, .move ⟨.scalar, .int .u 32, [some 0], [.sharedSym 0]⟩⟩,
    ⟨none, .move ⟨.scalar, .int .u 32, [some 1], [.sharedSym 4]⟩⟩, ⟨none, .ret⟩] := by rfl

def sharedShadow : Function where
  name := "shadow"
  header := [".visible", ".entry", "shadow", "(", ")"]
  body := [
    .declaration [".reg", ".b32", "%r", "<", "2", ">"],
    .scope [.declaration [".shared", ".align", "16", ".b8", "smem", "[", "16", "]"],
      .instruction none "mov.u32" [.register "%r0", .symbol "smem"]],
    .instruction none "mov.u32" [.register "%r1", .symbol "smem"],
    .instruction none "ret" []]

-- The block's `smem` shadows the module's `.extern .shared smem` only inside the block.
example : (Decode.kernelIn [[".extern", ".shared", ".align", "16", ".b8", "smem", "[", "]"]]
    sharedShadow).map (·.code) = .ok [
    ⟨none, .move ⟨.scalar, .int .u 32, [some 0], [.sharedSym 0]⟩⟩,
    ⟨none, .move ⟨.scalar, .int .u 32, [some 1], [.sharedSym 16]⟩⟩, ⟨none, .ret⟩] := by rfl

-- Two `.shared` variables of one name in one scope are an error (ptxas: duplicate definition).
example : (Decode.kernel { sharedSiblings with body := [
    .declaration [".shared", ".align", "4", ".b8", "buf", "[", "4", "]"],
    .declaration [".shared", ".align", "4", ".b8", "buf", "[", "4", "]"],
    .instruction none "ret" []] }).isOk = false := by rfl

/-! Comma lists of register names (§9.3: "predicate registers can be declared as .reg .pred p,
q, r;"): each name is one register of the type, in source order, scoped like the others. -/

example : Decode.regClass [".reg", ".b32", "a", ",", "b", ",", "c"] =
    .ok [⟨"a".toList, 0, 32⟩, ⟨"b".toList, 0, 32⟩, ⟨"c".toList, 0, 32⟩] := by rfl
example : (Decode.regClass [".reg", ".b32", "a", ",", "b", "<", "4", ">"]).isOk = false := by rfl
example : (Decode.regClass [".reg", ".b32", "a", ","]).isOk = false := by rfl
example : (Decode.regClass [".reg", ".b32", "a", ",", ",", "b"]).isOk = false := by rfl
example : (Decode.regClass [".reg", ".b32", "a", "b"]).isOk = false := by rfl

def commaList : Function where
  name := "comma"
  header := [".visible", ".entry", "comma", "(", ")"]
  body := [
    .declaration [".reg", ".b32", "%r", "<", "1", ">"],
    .scope [.declaration [".reg", ".b32", "lo", ",", "hi"],
      .instruction none "mov.b32" [.symbol "hi", .literal "7"],
      .instruction none "mov.b32" [.register "%r0", .symbol "hi"]],
    .declaration [".reg", ".pred", "p", ",", "q"],
    .instruction none "ret" []]

example : Decode.kernel commaList = .ok {
    name := "comma", params := [], regNames := ["%r0", "#/1#lo", "#/1#hi", "p", "q"], code := [
      ⟨none, .move ⟨.scalar, .int .b 32, [some 2], [.imm 7]⟩⟩,
      ⟨none, .move ⟨.scalar, .int .b 32, [some 0], [.reg 2]⟩⟩,
      ⟨none, .ret⟩]} := by rfl

-- A name listed twice is declared twice in one scope.
example : (Decode.kernel { commaList with body := [
    .declaration [".reg", ".b32", "a", ",", "a"], .instruction none "ret" []] }).isOk = false :=
  by rfl

end PTX.Tests.Scopes
