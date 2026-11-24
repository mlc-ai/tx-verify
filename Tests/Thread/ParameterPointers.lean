-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Fin.VecNotation
public import Core.Thread.Run
public import Core.Source.Decode

namespace PTX.Tests.ParameterPointers
noncomputable section

private def decl : ParamObjectDecl := ⟨"map", 8, 128, 128⟩
private def descriptor : TensorDescriptor.Descriptor 1 :=
  ⟨.f16, 4096, ![8192, 8192], ![16384], ⟨![64, 128], ![1, 1]⟩, .b128, .zero, .small⟩
private def L : Launch := {
  grid := 1, block := 128, params := fun _ => some 99
  paramObjects := fun name => if name = "map" then some (decl, 1024) else none
  tensorMaps := fun a => if a = 1024 then some ⟨1, descriptor⟩ else none }
private def t : TState := { regs := fun
  | 3 => some (.ptr 64 false (.param "map") 0)
  | 1 => some (.ptr 64 true (.param "map") 0)
  | 4 => some (.bits 64 1024)
  | 2 => some (.bits 32 0)
  | 6 => some (.bits 32 64)
  | _ => none }

-- Taking an address does not load the scalar value 99 supplied above.
example : readValue L 0 t 64 (.paramSym "map") = .ok (.ptr 64 false (.param "map") 0) := rfl
example : execLocal L 0 t (.move ⟨.scalar, .int .b 64, [some 5], [.paramSym "map"]⟩) =
    .ok (next (setReg t 5 (.ptr 64 false (.param "map") 0))) := rfl
example : execLocal L 0 t (.addr (.cvta false .param 64 5 (.reg 3))) =
    .ok (next (setReg t 5 (.ptr 64 true (.param "map") 0))) := rfl
example : execLocal L 0 t (.addr (.cvta true .param 64 5 (.reg 1))) =
    .ok (next (setReg t 5 (.ptr 64 false (.param "map") 0))) := rfl
example : execLocal L 0 t (.addr (.cvta false .param 64 5 (.reg 1))) = .error .badValue := rfl
example : execLocal L 0 t (.addr (.cvta true .param 64 5 (.reg 4))) = .error .badValue := rfl
example : readBits L 0 t 64 (.reg 1) = .error .noRule := rfl
-- A tensor map operand away from the base of the parameter object is not its address.
example : tensorMapAddress L 0 { regs := fun _ => some (.ptr 64 true (.param "map") 8) } (.reg 1) =
    .error .badValue := rfl

example : tensorMapAddress L 0 t (.reg 1) = .ok 1024 := rfl
example : tensorMapAddress L 0 t (.reg 3) = .error .badValue := rfl
example : tensorMapAddress { L with paramObjects := fun _ => none } 0 t (.reg 1) =
    .error .badParam := rfl
example : tensorMapAddress { L with paramObjects := fun _ =>
                                    some ({ decl with count := 64 }, 1024) }
    0 t (.reg 1) = .error .badParam := rfl
example : tensorMapAddress { L with paramObjects := fun _ => some (decl, 1025) }
    0 t (.reg 1) = .error .badParam := rfl

-- The production input path consumes the resolved object's descriptor and issues a copy.
example : tensorTmpl L 0 t
    (.cpTensor false false 2 0 (.reg 1) [(.imm 0), (.imm 0)] 6 0 none .tile) =
    .tensorIssue 1024 ⟨⟨1, descriptor, fun _ => 0, ⟨.shared, 0, 0⟩, none⟩, ⟨.shared, 0, 64⟩, false,
      .one⟩ (next t) := by
  change Tmpl.tensorIssue 1024
    ⟨⟨1, descriptor, (fun axis : Fin 2 => (BitVec.ofNat 32 (([truncBits 32 (BitVec.ofInt 64 (0)),
      truncBits 32 (BitVec.ofInt 64 (0))] : List (BitVec 64)).getD axis.val 0).toNat).toInt),
      ⟨.shared, 0, 0⟩, none⟩, ⟨.shared, 0, 64⟩, false, .one⟩ (next t) = _
  have h : (fun axis : Fin 2 => (BitVec.ofNat 32 (([truncBits 32 (BitVec.ofInt 64 (0)),
    truncBits 32 (BitVec.ofInt 64 (0))] : List (BitVec 64)).getD axis.val 0).toNat).toInt) =
    fun _ => 0 := by
    funext axis; rcases axis with ⟨_ | _ | _, h⟩ <;> rfl
  rw [h]

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 0, 64⟩], labels := [], params := [("map", 1024)] }
example : Decode.op env "mov.b64" [.register "r", .symbol "map"] =
    .ok (.move ⟨.scalar, .int .b 64, [some 0], [.paramSym "map"]⟩) := rfl
example : Decode.op env "cvta.param.u64" [.register "r", .symbol "map"] =
    .ok (.addr (.cvta false .param 64 0 (.paramSym "map"))) := rfl
example : Decode.op env "cvta.to.param::entry.u64" [.register "r", .register "r"] =
    .ok (.addr (.cvta true .param 64 0 (.reg 0))) := rfl

end
end PTX.Tests.ParameterPointers
