-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Assembly.Correctness
public import Core.Source.Decode
public import Mathlib.Tactic

namespace PTX.Tests.TensorThread
noncomputable section

private def descriptor : TensorDescriptor.Descriptor 1 :=
  ⟨.f16, 4096, ![8192, 8192], ![16384], ⟨![64, 128], ![1, 1]⟩, .b128, .zero, .small⟩
private def L : Launch := {
  grid := 2, block := 128, params := fun _ => none, clusterSize := ⟨2, by decide⟩,
  tensorMaps := fun address => if address = 1024 then some ⟨1, descriptor⟩ else none }
private def t : TState := { regs := fun
  | 0 => some (.bits 32 128)
  | 1 => some (.ptr 32 false (.shared 1 0) 64)
  | 2 => some (.bits 64 1024)
  | _ => none }
private def op : Op := .cpTensor true true 0 0 (.reg 2) [(.imm (-8)), (.imm 32)] 1 0 none .tile
private def spec : TensorCopy.Spec :=
  ⟨⟨1, descriptor, ![-8, 32], ⟨.shared, 1, 128⟩, none⟩, ⟨.shared, 0, 64⟩, true, .two⟩
private def env : Decode.Env :=
  { classes := [⟨"r".toList, 2, 32⟩, ⟨"rd".toList, 1, 64⟩], labels := [], params := [] }

example : Decode.op env
    "cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes.cta_group::2"
    [.address [.register "r0"], .address [.register "rd0", .vector [.literal "-8", .literal "32"]],
      .address [.register "r1"]] = .ok op := rfl
example : Decode.op env
    "cp.async.bulk.tensor.2d.shared::cta.global.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", .vector [.literal "0", .literal "32"]],
      .address [.register "r1"]] =
    .ok (.cpTensor false false 0 0 (.reg 2) [(.imm 0), (.imm 32)] 1 0 none .tile) := rfl

-- Negative coordinates survive as signed values (-8 f16 elements are 16 bytes) and do not wrap.
private theorem issue_eq : tensorTmpl L 128 t op = .tensorIssue 1024 spec (next t) := by
  change Tmpl.tensorIssue 1024 { spec with origin := (fun axis : Fin 2 =>
                                           (BitVec.ofNat 32 (([truncBits 32 (BitVec.ofInt 64 (-8)),
    truncBits 32 (BitVec.ofInt 64 (32))] : List (BitVec 64)).getD axis.val 0).toNat).toInt) }
    (next t) = _
  have h : (fun axis : Fin 2 => (BitVec.ofNat 32 (([truncBits 32 (BitVec.ofInt 64 (-8)),
    truncBits 32 (BitVec.ofInt 64 (32))] : List (BitVec 64)).getD axis.val 0).toNat).toInt) =
    spec.origin := by
    funext axis
    fin_cases axis <;> rfl
  rw [h]
example : eventTmpl [] L 128 t op = .tensorIssue 1024 spec (next t) := issue_eq
example : op.isLocal = false := rfl
example : tensorTmpl { L with tensorMaps := fun _ => none } 128 t op = .ub .noRule := rfl
example : tensorTmpl L 128 t
    (.cpTensor true false 0 0 (.reg 2) [(.imm 0), (.imm 32)] 1 0 none .tile) =
    .ub .badValue := rfl
example : tensorTmpl L 128 t
    (.cpTensor true true 0 1 (.reg 2) [(.imm 0), (.imm 32)] 1 0 none .tile) =
    .ub .misaligned := rfl

-- Issuing a tensor copy creates a drain obligation even before any effects exist.
private def X : Execution := {
  tr := fun g => if g = 128 then [⟨0, .tensorIssue 1024 spec⟩] else [],
  rf := fun _ _ => none }
example : ¬ AsyncDrained X := by
  intro h
  obtain ⟨o, ho, _⟩ := ((asyncDrained_iff X).1 h).2.2.2.2.1 (128, 0) 1024 spec ⟨0, by rfl⟩
  cases ho

end
end PTX.Tests.TensorThread
