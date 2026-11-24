-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Thread.Local
public import Core.Async.Tma

/-! `createpolicy` (THREAD-CACHE-POLICY, §9.7.10.21), `nanosleep` and `pmevent` (THREAD-NO-EFFECT,
§9.7.21.2, §9.7.21.3): decoding, the rule of each form, evaluation and rejected cases. -/
namespace PTX.Tests.MiscForms
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 2, 64⟩], labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %rd0..%rd1 = 4..5
private def r (n : String) : Syntax.Operand := .register n
private def addr (n : String) : Syntax.Operand := .address [.register n]

/-! ## Decoding -/

example : Decode.op env "createpolicy.fractional.L2::evict_last.b64" [r "%rd0"] =
    .ok (.misc (.createPolicy 4 (.fraction none))) := rfl
example : Decode.op env "createpolicy.fractional.L2::evict_last.L2::evict_unchanged.b64"
    [r "%rd0", r "%r1"] = .ok (.misc (.createPolicy 4 (.fraction (some (.reg 1))))) := rfl
example : Decode.op env "createpolicy.range.global.L2::evict_last.L2::evict_first.b64"
    [r "%rd0", addr "%rd1", r "%r0", r "%r1"] =
    .ok (.misc (.createPolicy 4 (.range true ⟨.reg 5 64, 0⟩ (.reg 0) (.reg 1)))) := rfl
example : Decode.op env "createpolicy.cvt.L2.b64" [r "%rd0", r "%rd1"] =
    .ok (.misc (.createPolicy 4 (.cvt (.reg 5)))) := rfl
example : Decode.op env "nanosleep.u32" [.literal "42"] = .ok (.misc (.nanosleep (.imm 42))) :=
  rfl
example : Decode.op env "nanosleep.u32" [r "%r0"] = .ok (.misc (.nanosleep (.reg 0))) := rfl
example : Decode.op env "pmevent" [.literal "7"] = .ok (.misc (.pmevent false 7)) := rfl
example : Decode.op env "pmevent.mask" [.literal "0xff"] = .ok (.misc (.pmevent true 255)) := rfl
-- Rejected: a `pmevent` index above 15 and a mask above 16 bits.
example : (Decode.op env "pmevent" [.literal "16"]).isOk = false := rfl
example : (Decode.op env "pmevent.mask" [.literal "0x10000"]).isOk = false := rfl

example : Op.rule (.misc (.createPolicy 4 (.fraction none))) = some .threadCachePolicy := rfl
example : Op.rule (.misc (.nanosleep (.imm 42))) = some .threadNoEffect := rfl
example : Op.rule (.misc (.pmevent true 255)) = some .threadNoEffect := rfl

/-! ## Evaluation -/

-- The policy is the opaque value.
example : execLocal launch 0 {} (.misc (.createPolicy 4 (.fraction none))) =
    .ok (next (setReg {} 4 .policy)) := rfl
example : execLocal launch 0 {} (.misc (.createPolicy 4 (.cvt (.imm 7)))) =
    .ok (next (setReg {} 4 .policy)) := rfl
example : execLocal launch 0 {}
    (.misc (.createPolicy 4 (.range true ⟨.imm 4096, 0⟩ (.imm 256) (.imm 1024)))) =
    .ok (next (setReg {} 4 .policy)) := rfl
-- The primary size must be at most the total size.
example : execLocal launch 0 {}
    (.misc (.createPolicy 4 (.range true ⟨.imm 4096, 0⟩ (.imm 2048) (.imm 1024)))) =
    .error .badValue := rfl
-- A shared address has no rule.
example : execLocal launch 0 {}
    (.misc (.createPolicy 4 (.range false ⟨.sharedSym 0, 0⟩ (.imm 0) (.imm 1)))) =
    .error .noRule := rfl
-- The policy has no bit pattern: an integer reading of it has no rule.
example : readBits launch 0 (setReg {} 4 .policy) 64 (.reg 4) = .error .noRule := rfl
-- A bulk copy's `cache_policy` operand accepts it.
example : bulkPolicy launch 0 (setReg {} 4 .policy) (some (.reg 4)) = .ok () := rfl

example : execLocal launch 0 {} (.misc (.nanosleep (.imm 42))) = .ok (next {}) := rfl
example : execLocal launch 0 {} (.misc (.pmevent false 7)) = .ok (next {}) := rfl
-- Rejected: a delay in a register that was never written.
example : execLocal launch 0 {} (.misc (.nanosleep (.reg 0))) = .error .uninitialized := rfl

end
end PTX.Tests.MiscForms
