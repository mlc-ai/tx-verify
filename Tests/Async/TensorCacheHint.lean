-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode

/-! The `.L2::cache_hint` form of a tensor load (THREAD-TENSOR-ISSUE): the 64-bit cache policy is
decoded and must be a defined value, and it changes nothing else (§9.7.10.28.5.3: "It is
treated as a performance hint only, and does not change the memory consistency behavior of the
program."). -/
namespace PTX.Tests.TensorCacheHint
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 4, 32⟩, ⟨"rd".toList, 2, 64⟩], labels := [], params := [] }
private def args : List Syntax.Operand :=
  [.address [.offset "+" (.register "r0") (.literal "134144")],
    .address [.register "rd0", .vector [.literal "0", .register "r1", .register "r2",
      .register "r3"]],
    .address [.register "r1"]]
private def load (policy : Option Opnd) : Op :=
  .cpTensor true true 0 134144 (.reg 4) [.imm 0, .reg 1, .reg 2, .reg 3] 1 0 none .tile policy

-- FA4's form: the hint written after `.cta_group::2`, and in the syntax's order before it.
example : Decode.op env ("cp.async.bulk.tensor.4d.shared::cluster.global.tile." ++
    "mbarrier::complete_tx::bytes.L2::cache_hint.cta_group::2") (args ++ [.register "rd1"]) =
    .ok (load (some (.reg 5))) := rfl
example : Decode.op env ("cp.async.bulk.tensor.4d.shared::cluster.global.tile." ++
    "mbarrier::complete_tx::bytes.cta_group::2.L2::cache_hint") (args ++ [.register "rd1"]) =
    .ok (load (some (.reg 5))) := rfl
-- Without the hint the form is the existing one.
example : Decode.op env ("cp.async.bulk.tensor.4d.shared::cluster.global.tile." ++
    "mbarrier::complete_tx::bytes.cta_group::2") args = .ok (load none) := rfl
-- With multicast, the mask comes before the policy.
example : Decode.op env ("cp.async.bulk.tensor.2d.shared::cluster.global." ++
    "mbarrier::complete_tx::bytes.multicast::cluster.L2::cache_hint")
    [.address [.register "r0"], .address [.register "rd0", .vector [.literal "0", .literal "0"]],
      .address [.register "r1"], .literal "3", .register "rd1"] =
    .ok (.cpTensor true false 0 0 (.reg 4) [.imm 0, .imm 0] 1 0 (some (16, .imm 3)) .tile
      (some (.reg 5))) := rfl
-- Rejected: the qualifier without its operand, the operand without the qualifier, the
-- qualifier twice, a 32-bit policy register.
example : (Decode.op env ("cp.async.bulk.tensor.4d.shared::cluster.global.tile." ++
    "mbarrier::complete_tx::bytes.L2::cache_hint.cta_group::2") args).toOption = none := rfl
example : (Decode.op env ("cp.async.bulk.tensor.4d.shared::cluster.global.tile." ++
    "mbarrier::complete_tx::bytes.cta_group::2") (args ++ [.register "rd1"])).toOption =
    none := rfl
example : (Decode.op env ("cp.async.bulk.tensor.4d.shared::cluster.global.tile." ++
    "mbarrier::complete_tx::bytes.L2::cache_hint.cta_group::2.L2::cache_hint")
    (args ++ [.register "rd1"])).toOption = none := by decide +kernel
example : (Decode.op env ("cp.async.bulk.tensor.4d.shared::cluster.global.tile." ++
    "mbarrier::complete_tx::bytes.L2::cache_hint.cta_group::2")
    (args ++ [.register "r1"])).toOption = none := rfl

/-! ## Issue: the policy is read and otherwise unused -/

private def L : Launch := { grid := 2, block := 128, params := fun _ => none, clusterSize := 2 }
private def t (policy : Option Value) : TState := { regs := fun
  | 5 => policy
  | _ => none }

-- An undefined policy register faults before anything else is read.
example : tensorTmpl L 0 (t none) (load (some (.reg 5))) = .ub .uninitialized := rfl
-- A defined policy (FA4 passes 0) leaves the instruction's template that of the form without it.
example : tensorTmpl L 0 (t (some (.bits 64 0))) (load (some (.reg 5))) =
    tensorTmpl L 0 (t (some (.bits 64 0))) (load none) := rfl
example (v : BitVec 64) :
    tensorTmpl L 0 (t (some (.bits 64 v))) (load (some (.reg 5))) =
      tensorTmpl L 0 (t (some (.bits 64 v))) (load none) := rfl

end
end PTX.Tests.TensorCacheHint
