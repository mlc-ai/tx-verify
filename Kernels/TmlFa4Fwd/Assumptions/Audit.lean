-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public meta import Kernels.TmlFa4Fwd.Assumptions
public meta import Kernels.TmlFa4Fwd.Data.Decoded
public meta import Kernels.FlashAttn4Fwd.Assumptions.Exp2Template
public meta import Assumption.ApproxExact
public meta import Core.Tc.TcMmaDescriptor
public meta import Lean.Elab.Tactic.ElabTerm

open PTX PTX.Assumption PTX.Kernels.TmlFa4Fwd
open PTX.Kernels.TmlFa4Fwd.Assumptions

/-- Project the executable bodies from the FA4 shapes, whose constants mention model values. -/
private def exp2DefineBody : List (SegInstr CuteSlot) := by
  run_tac
    let body ← Lean.Elab.Term.elabTerm (← `(cuteExp2Define.body)) none
    Lean.Elab.Tactic.closeMainGoal `exact (← Lean.Meta.whnf body)

private def exp2ReuseBody : List (SegInstr CuteSlot) := by
  run_tac
    let body ← Lean.Elab.Term.elabTerm (← `(cuteExp2Reuse.body)) none
    Lean.Elab.Tactic.closeMainGoal `exact (← Lean.Meta.whnf body)

private theorem exp2DefineBody_eq : exp2DefineBody = cuteExp2Define.body := rfl
private theorem exp2ReuseBody_eq : exp2ReuseBody = cuteExp2Reuse.body := rfl

/- Audit the local selectors and the shape of every software exponentiation in the frozen entry. -/
#eval show IO Unit from do
  let code := Decoded.kernel.code
  let pcs (selects : Instr → Bool) :=
    code.zipIdx.filterMap fun (i, pc) => if selects i then some pc else none
  unless pcs (fun i => (lg2Operands i.op).isSome) == lg2Sites do
    throw (IO.userError "lg2 site mismatch")
  unless pcs (fun i => (biasWidenOperands i.op).isSome) == biasWidenSites do
    throw (IO.userError "BF16 bias widening site mismatch")
  unless pcs (fun i => (probPackOperands i.op).isSome) == probPackSites do
    throw (IO.userError "BF16 probability packing site mismatch")
  let clamps := pcs fun i =>
    (SegInstr.maxF32 CuteSlot.m0 CuteSlot.x0 0xC2FE0000).bind i |>.isSome
  unless clamps == swExp2Sites.flatMap (fun pc => [pc, pc + 1]) do
    throw (IO.userError "software exp2 clamp site mismatch")
  let targets := code.flatMap fun i => match i.op with
    | .bra target _ => [target]
    | .brx _ targets _ => targets
    | _ => []
  for pc in swExp2Sites do
    let defines := pc == 6059 || pc == 7090
    let body := if defines then exp2DefineBody else exp2ReuseBody
    unless (matchBody body (code.drop pc) []).isSome do
      throw (IO.userError s!"software exp2 template mismatch at {pc}")
    if targets.any (fun target => pc < target && target < pc + body.length) then
      throw (IO.userError s!"branch into software exp2 template at {pc}")
  let counts := arithScope.float.map fun f => (pcs fun i => FloatForm.ofOp i.op == some f).length
  unless counts == [3, 9, 2, 2, 191, 32, 256, 368, 230, 7, 3] do
    throw (IO.userError s!"ideal arithmetic counts: {counts}")
  let ex2 := pcs fun i => ApproxForm.ofOp i.op == some (.ex2 .f32)
  let rcp := pcs fun i => ApproxForm.ofOp i.op == some (.rcp .f32)
  unless ex2.length == 450 && rcp == [8471, 8767] do
    throw (IO.userError "hardware exp2 or rcp site mismatch")
  for pc in ex2 ++ rcp do
    unless code[pc]?.any (fun i => match i.op with
      | .float f => f.ftz && f.srcTys.isEmpty && f.srcs.length == 1 && f.dsts.length == 1
      | _ => false) do
      throw (IO.userError s!"hardware exp2 or rcp operand mismatch at {pc}")
  let neg := pcs fun i => match i.op with
    | .float f => f.op == .neg
    | _ => false
  unless neg == [4398] do throw (IO.userError "floating negation site mismatch")
  let onBiasBranch := code[5815]?.any fun i => i.guard.isSome && match i.op with
    | .bra 5977 false => true
    | _ => false
  unless onBiasBranch do throw (IO.userError "biased software exp2 branch mismatch")
  let mmas := code.zipIdx.filterMap fun (i, pc) => match i.op with
    | .tcMma m => some (m, pc)
    | _ => none
  unless mmas.length == 64 do throw (IO.userError "tcgen05.mma site count mismatch")
  for (m, pc) in mmas do
    let desc : Option TcMma.Descriptor := do
      let .reg reg := m.idesc | none
      let bits ← (code.take pc).reverse.findSome? fun (i : Instr) => do
        let .move mov := i.op | none
        let ([some dst], [.imm bits]) := (mov.dsts, mov.srcs) | none
        if dst == reg && i.guard.isNone && mov.ty == .int .b 32 then some bits.toNat else none
      TcMma.decode m.group m.ws m.kind bits
    unless m.group == .one && (desc.any fun d => arithScope.mma.contains d.kind) do
      throw (IO.userError s!"tcgen05.mma descriptor mismatch at {pc}")

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Assumptions

/- The patched biased loop switches to hardware for key blocks at or above
`(tileStart + kLength - qLength) / 128` (patched `block_info.py:149–167`,
`flash_fwd_sm100.py:3369–3404`). The PTX tests this bound at pc 5535, and the branch at
pc 5815 reaches the first eight template sites. The unbiased loop reaches the following
eight sites without that test. For Q length 129 and K length 4096, the first tile's cutoff
is 30 and biased block 29 is software-eligible. The second Q stage of that tile reads the
packed bias columns 896–1023 for block 29, including from the following request's row if it
has length 1. With K length 1, that request's own packed columns start at 1152, so its bias
in columns 896–1023 can contain negative infinity. -/

/-- The packed add is exact at the clamp, and both subtractions recover an exact zero
fraction. The three fused polynomial steps at zero therefore return the constant 1. -/
theorem swExp2ClampNumbers :
    f32Value 0xC2FE0000 = some (-127) ∧
    f32Value 0x4B400000 = some 12582912 ∧
    f32Value 0x4B3FFF81 = some (12582912 - 127) ∧
    f32Value 0x3F800000 = some 1 := by
  decide +kernel

/-- The exponent construction on the clamped negative-infinity lane gives positive zero. -/
theorem swExp2ClampBits :
    ((0x4B3FFF81 : BitVec 32) <<< 23) + 0x3F800000 = 0 := by
  decide +kernel

end PTX.Kernels.TmlFa4Fwd.Assumptions
