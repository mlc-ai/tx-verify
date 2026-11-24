-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Thread.Access
public import Core.Async.Tma
public import Core.Source.Decode

namespace PTX.Tests.SharedPointer
noncomputable section

private def launch : Launch := { grid := 4, block := 384, clusterSize := 2, params := fun _ =>
                                 none }
private def env : Decode.Env :=
  { classes := [⟨"r".toList, 3, 32⟩, ⟨"rd".toList, 3, 64⟩], labels := [], params := [] }

example : Decode.op env "mapa.shared::cluster.u32"
    [.register "r0", .register "r1", .register "r2"] =
    .ok (.addr (.mapa false 32 0 (.reg 1) (.reg 2))) := rfl
example : Decode.op env "mapa.u64"
    [.register "rd0", .register "rd1", .register "r2"] =
    .ok (.addr (.mapa true 64 3 (.reg 4) (.reg 2))) := rfl
example : Decode.op env "cvta.to.shared::cluster.u64"
    [.register "rd0", .register "rd1"] =
    .ok (.addr (.cvta true (.shared .cluster) 64 3 (.reg 4))) := rfl
example : Decode.op env "cvta.to.shared.u64"
    [.register "rd0", .register "rd1"] =
    .ok (.addr (.cvta true (.shared .cta) 64 3 (.reg 4))) := rfl

private def start : TState := { regs := fun r => if r = 16 then some (.bits 32 128) else none }
private def peer (g : Nat) : Exec TState :=
  execLocal launch g start (.addr (.mapa false 32 12 (.reg 16) (.imm 0)))

-- Rank zero is relative to the issuer's cluster: CTA 3 maps to CTA 2, and the pointer records
-- its producer, CTA 3.
example : (peer (3 * 384)).map (fun t => t.regs 12) =
    .ok (some (.ptr 32 false (.shared 3 2) 128)) := rfl
-- The producer uses its mapa result: it resolves to the peer CTA.
example : ((peer (3 * 384)).bind fun t => sharedEffAddr launch (3 * 384) t true 12 8) =
    .ok ⟨.shared, 2, 136⟩ := rfl
-- Another thread of the producing CTA may use it too.
example : ((peer (3 * 384)).bind fun t => sharedEffAddr launch (3 * 384 + 5) t true 12 0) =
    .ok ⟨.shared, 2, 128⟩ := rfl
example : execLocal launch 0 start (.addr (.mapa false 32 12 (.reg 16) (.imm 2))) =
    .error .badValue := rfl
example : execLocal launch 0 start (.addr (.mapa true 32 12 (.reg 16) (.imm 0))) =
    .error .noRule := rfl

private def converted (g : Nat) (cluster : Bool) : Exec TState := do
  let t ← execLocal launch g {} (.move ⟨.scalar, .int .u 64, [some 15], [.imm 128]⟩)
  let t ← execLocal launch g t (.addr (.cvta false (.shared .cta) 64 14 (.reg 15)))
  let t ← execLocal launch g t (.int ⟨.add, .int .u 64, false, [some 13], [.reg 14, .imm 8]⟩)
  let t ← execLocal launch g t (.addr (.mapa true 64 12 (.reg 13) (.imm 0)))
  let t ← execLocal launch g t
    (.addr (.cvta true (.shared (if cluster then .cluster else .cta)) 64 11 (.reg 12)))
  let t ← execLocal launch g t
    (.cvt { dst := .int .u 32, src := .int .u 64, d := 10, srcs := [.reg 11] })
  execLocal launch g t (.int ⟨.add, .int .u 32, false, [some 9], [.reg 10, .imm 8]⟩)

-- The real sequence of conversion, generic pointer addition, mapa, conversion,
-- narrowing and shared pointer addition retains the target and producing CTA.
example : (converted (3 * 384) true).map (fun t => t.regs 9) =
    .ok (some (.ptr 32 false (.shared 3 2) 144)) := rfl
-- `cvta.to.shared{::cta}` yields the `.shared::cta` window address: a number.
example : (converted (2 * 384) false).map (fun t => t.regs 11) =
    .ok (some (.bits 64 136)) := rfl
example : (converted (2 * 384) false).map (fun t => t.regs 9) =
    .ok (some (.bits 32 144)) := rfl
-- Omitted cvta sub-qualifier is ::cta, not ::cluster. A peer pointer is rejected.
example : converted (3 * 384) false = .error .badValue := rfl

private def remote : TState := {
  regs := fun r => if r = 7 then some (.ptr 32 false (.shared 3 2) 144) else none
}
example : sharedEffAddr launch (3 * 384) remote true 7 8 =
    .ok ⟨.shared, 2, 152⟩ := rfl
-- As a `.shared::cta` operand a `.shared::cluster` pointer has no rule, whichever CTA it names.
example : effAddr launch (3 * 384) remote .shared 7 8 = .error .noRule := rfl
example : readBits launch 0 remote 32 (.reg 7) = .error .noRule := rfl
-- A cluster pointer made by CTA 0 for CTA 2 of another cluster is rejected for its producer.
private def foreign : TState := {
  regs := fun r => if r = 7 then some (.ptr 32 false (.shared 0 2) 144) else none
}
example : sharedEffAddr launch 0 foreign true 7 0 = .error .badValue := rfl

-- A symbolic pointer is used only in the CTA that produced it (THREAD-SHARED-POINTER): the
-- text does not say what CTA 0's `.shared::cluster` or generic address denotes in CTA 1. CTA 0
-- maps its own byte 0x100 into the cluster window, stores the pointer, and CTA 1 loads it back
-- and uses it as an mbarrier address: no rule.
private def own0 : TState := { regs := fun r => if r = 0 then some (.bits 32 0x100) else none }
private def made0 : Exec Value := do
  let t ← execLocal launch 0 own0 (.addr (.cvta false (.shared .cta) 32 1 (.reg 0)))
  let t ← execLocal launch 0 t (.addr (.cvta true (.shared .cluster) 32 2 (.reg 1)))
  let some v := t.regs 2 | throw .noRule
  pure v
example : made0 = .ok (.ptr 32 false (.shared 0 0) 0x100) := rfl
-- The stored bytes rebuild the same pointer.
example : rebuild 4 ((Value.ptr 32 false (.shared 0 0) 0x100).toBytes.map some) =
    .ok (.ptr 32 false (.shared 0 0) 0x100) := by
  simp [rebuild, Value.toBytes, Value.bytes, Value.byteAt, List.range_succ]
  rfl
private def held1 : TState := {
  regs := fun r => if r = 0 then some (.ptr 32 false (.shared 0 0) 0x100) else none
}
example : sharedEffAddr launch 384 held1 true 0 0 = .error .noRule := rfl
example : mbarClusterLoc launch 384 held1 0 0 = .error .noRule := rfl
-- Its producer resolves it.
example : sharedEffAddr launch 0 held1 true 0 0 = .ok ⟨.shared, 0, 0x100⟩ := rfl
-- The same number as a raw `.shared::cta` address names the executing CTA's byte, in CTA 1.
private def raw1 : TState := { regs := fun r => if r = 0 then some (.bits 32 0x100) else none }
example : sharedEffAddr launch 384 raw1 true 0 0 = .ok ⟨.shared, 1, 0x100⟩ := rfl
-- `cvta.to.shared` of CTA 0's own generic pointer is that number, not a tagged pointer.
private def gen0 : TState := {
  regs := fun r => if r = 0 then some (.ptr 32 true (.shared 0 0) 0x100) else none
}
example : (execLocal launch 0 gen0 (.addr (.cvta true (.shared .cta) 32 1 (.reg 0)))).map
    (fun t => t.regs 1) = .ok (some (.bits 32 0x100)) := rfl
-- A generic pointer of CTA 0 converted by CTA 1 has no rule either.
example : execLocal launch 384 gen0 (.addr (.cvta true (.shared .cta) 32 1 (.reg 0))) =
    .error .noRule := rfl

-- Ordinary moves preserve the opaque pointer. Integer pointer-bit extraction is not invented.
example : (execLocal launch (3 * 384) remote
    (.move ⟨.scalar, .int .u 32, [some 8], [.reg 7]⟩)).map
    (fun t => t.regs 8) = .ok (some (.ptr 32 false (.shared 3 2) 144)) := rfl
example : (execLocal launch (3 * 384) remote
    (.int ⟨.sub, .int .u 32, false, [some 6], [.reg 7, .imm 8]⟩)).map
    (fun t => t.regs 6) = .ok (some (.ptr 32 false (.shared 3 2) 136)) := rfl
example : offsetPointer 32 (.ptr 32 false (.shared 3 2) 0) (-1) = .error .noRule := rfl

end
end PTX.Tests.SharedPointer
