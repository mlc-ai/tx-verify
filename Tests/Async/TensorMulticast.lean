-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.Tensor.TensorMulticast
public import Mathlib.Tactic

/-! `.multicast::cluster` tensor loads (THREAD-TENSOR-ISSUE `tensorMulticast`): one copy per
ctaMask rank, in rank order through sub-steps, each with its data and mbarrier at the same
CTA-relative offsets. `Tools/probes/tma_mc.ptx` (one 4-CTA cluster, masks 0xF, 0x5, 0xA, 0xE,
0x1) matched every CTA's buffer byte for byte on a B200, and every masked CTA's mbarrier
completed on its own transaction count. -/
namespace PTX.Tests.TensorMulticast
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 4, 32⟩, ⟨"rd".toList, 2, 64⟩, ⟨"rs".toList, 2, 16⟩], labels := [],
      params := [] }

/-! ## Decoding -/

example : Decode.op env
    "cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes.multicast::cluster"
    [.address [.register "r0"], .address [.register "rd0", .vector [.literal "32", .literal "5"]],
      .address [.register "r1"], .register "rs1"] =
    .ok (.cpTensor true false 0 0 (.reg 4) [.imm 32, .imm 5] 1 0 (some (16, .reg 7)) .tile) :=
  rfl
example : Decode.op env
    "cp.async.bulk.tensor.3d.shared::cluster.global.mbarrier::complete_tx::bytes.\
      multicast::cluster::32b.cta_group::2"
    [.address [.register "r0"], .address [.register "rd0", .vector [.literal "0", .literal "0",
      .literal "1"]],
      .address [.register "r1"], .register "r2"] =
    .ok (.cpTensor true true 0 0 (.reg 4) [.imm 0, .imm 0, .imm 1] 1 0 (some (32, .reg 2)) .tile) :=
  rfl
-- A multicast needs its ctaMask and a shared::cluster destination; a mask needs the qualifier.
example : (Decode.op env
    "cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes.multicast::cluster"
    [.address [.register "r0"], .address [.register "rd0", .vector [.literal "0", .literal "0"]],
      .address [.register "r1"]]).isOk = false := rfl
example : (Decode.op env
    "cp.async.bulk.tensor.2d.shared::cta.global.mbarrier::complete_tx::bytes.multicast::cluster"
    [.address [.register "r0"], .address [.register "rd0", .vector [.literal "0", .literal "0"]],
      .address [.register "r1"], .register "rs1"]).isOk = false := rfl
example : (Decode.op env
    "cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", .vector [.literal "0", .literal "0"]],
      .address [.register "r1"], .register "rs1"]).isOk = false := rfl

/-! ## Issue sub-steps: one copy per destination rank -/

private def d : TensorDescriptor.Descriptor 1 :=
  ⟨.u8, 4096, ![256, 64], ![256], ⟨![64, 8], ![1, 1]⟩, .none, .zero, .small⟩
/-- A 4-CTA cluster; the issuer is CTA 0 (rank 0 of cluster 0). -/
private def L : Launch := {
  grid := 8, block := 128, params := fun _ => none, clusterSize := ⟨4, by decide⟩,
  tensorMaps := fun address => if address = 1024 then some ⟨1, d⟩ else none }
private def regs (mask : Nat) : Nat → Option Value
  | 0 => some (.bits 32 1024)
  | 1 => some (.ptr 32 false (.shared 0 0) 64)
  | 4 => some (.bits 64 1024)
  | 7 => some (.bits 16 (BitVec.ofNat 64 mask))
  | _ => none
private def st (mask sub : Nat) : TState := { pc := 7, regs := regs mask, sub }
private def op (two : Bool) : Op :=
  .cpTensor true two 0 0 (.reg 4) [.imm 32, .imm 5] 1 0 (some (16, .reg 7)) .tile
/-- The copy's data CTA, mbarrier CTA and the continuation's (pc, sub step). -/
private def step : Tmpl → Option (Nat × Nat × Nat × Nat)
  | .tensorIssue _ s u => some (s.sharedBase.cta, s.mbar.cta, u.pc, u.sub)
  | _ => none

-- ctaMask 0b1010: ranks 1 and 3; the issuer's own CTA is not written.
example : step (tensorTmpl L 0 (st 0b1010 0) (op false)) = some (1, 1, 7, 1) := rfl
example : step (tensorTmpl L 0 (st 0b1010 1) (op false)) = some (3, 3, 8, 0) := rfl
example : tensorTmpl L 0 (st 0b1010 2) (op false) = .ub .badValue := rfl
-- A single destination finishes the instruction in one step.
example : step (tensorTmpl L 0 (st 0b0100 0) (op false)) = some (2, 2, 8, 0) := rfl
-- An empty mask, or a rank outside the cluster, has no copy.
example : tensorTmpl L 0 (st 0 0) (op false) = .ub .badValue := rfl
example : tensorTmpl L 0 (st 0b10001 0) (op false) = .ub .badValue := rfl
-- cta_group::2: each destination's signal goes to the CTA of its pair with the parity of
-- `mbar`'s CTA (here rank 0, even): rank 3's data with rank 2's mbarrier.
example : step (tensorTmpl L 0 (st 0b1010 1) (op true)) = some (3, 2, 8, 0) := rfl
example : step (tensorTmpl L 0 (st 0b1010 0) (op true)) = some (1, 0, 7, 1) := rfl
-- Every multicast step is a fault or one issue keeping the registers (`tensorTmpl_cpTensor_cases`).
example : ∀ sub < 3, step (tensorTmpl L 0 (st 0b1110 sub) (op false)) =
    [some (1, 1, 7, 1), some (2, 2, 7, 2), some (3, 3, 8, 0)].getD sub none := by decide

/-! ## The operands' CTAs (§9.7.10.28.5.3)

`mbar` must be in `dstMem`'s CTA (`.cta_group::1`) or its pair (`.cta_group::2`); the operands
are checked before the copies are fanned out. Here `dstMem` is in CTA 0. -/
private def stM (mbarCta : Nat) : TState :=
  { pc := 7, sub := 0, regs := fun r => if r = 1 then some (.ptr 32 false (.shared 0 mbarCta) 64)
      else regs 0b1010 r }
example : tensorTmpl L 0 (stM 2) (op false) = .ub .badValue := rfl
example : tensorTmpl L 0 (stM 1) (op false) = .ub .badValue := rfl
example : step (tensorTmpl L 0 (stM 1) (op true)) = some (1, 1, 7, 1) := rfl
example : tensorTmpl L 0 (stM 2) (op true) = .ub .badValue := rfl

end
end PTX.Tests.TensorMulticast
