-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Operand
public import Core.Isa.Rule
public import Core.Isa.Mem

@[expose] public section

/-!
# Miscellaneous instructions

The representation of `createpolicy`, `nanosleep` and `pmevent` and its construction from a
recognized instruction.
-/

namespace PTX

/-! ## PROG-ISA-MISC — cache policies, sleep and performance monitor events
Statement: A `createpolicy` is its destination register and the operands of its kind: the address
  and the two sizes of a range-based policy with whether `.global` is written, the optional fraction
  of a fraction-based policy, or the access property that `createpolicy.cvt` converts. `nanosleep`
  is its delay operand, `pmevent` its immediate with whether `.mask` is written, and
  `griddepcontrol` its action.

Defs: PolicyKind, MiscInstr, Decode.MiscInstr.ofRaw, MiscInstr.rule

Source:
- §9.7.10.21: "cache_policy, [a], primary-size, total-size;"
- §9.7.10.21: "cache_policy{, fraction};"
- §9.7.10.21: "createpolicy.cvt.L2.b64 cache_policy, access-property;"
- §9.7.10.21: "If no state space is specified then Generic Addressing is used."
- §9.7.21.2: "nanosleep.u32 t;"
- §9.7.21.2: "t may be a register or an immediate value."
- §9.7.21.3: "pmevent (without modifier .mask ) triggers a single performance monitor event indexed
    by immediate operand a , in the range 0..15 ."
- §9.7.21.3: "Each bit in the 16-bit immediate operand a controls an event."
- §9.7.15.14: "griddepcontrol.action; .action = { .launch_dependents, .wait }"

Direction: representation

Applies: `createpolicy`, `nanosleep`, `pmevent` and `griddepcontrol`

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at the
  widths of the operand types.

Effect: Representation; `MiscInstr.rule` selects THREAD-CACHE-POLICY for `createpolicy` and
  THREAD-NO-EFFECT for `nanosleep`, `pmevent` and `griddepcontrol`.
  The eviction priorities of `createpolicy` are not recorded, since no rule reads them
  (THREAD-CACHE-POLICY). A `pmevent` immediate outside 0 to 15, or a `pmevent.mask` immediate
  outside 16 bits, is rejected. `nanosleep` and `pmevent` are entries of the grammar's own
  (`Tools/isa/extra.py`), since the TIRx table has neither. The range form
  `createpolicy.range.fabric` is not in the table and is not recognized.
-/

/-- The operands of a `createpolicy` kind. -/
inductive PolicyKind where
  /-- `createpolicy.range{.global}`: the address `[a]`, `primary-size` and `total-size`;
  `global` when `.global` is written. -/
  | range (global : Bool) (a : Addr) (primary total : Opnd)
  /-- `createpolicy.fractional` with its optional `fraction`. -/
  | fraction (f : Option Opnd)
  /-- `createpolicy.cvt.L2` with its `access-property`. -/
  | cvt (a : Opnd)
  deriving DecidableEq, Repr

/-- A miscellaneous instruction. -/
inductive MiscInstr where
  | createPolicy (d : Nat) (k : PolicyKind)
  | nanosleep (t : Opnd)
  | pmevent (mask : Bool) (a : Nat)
  /-- `griddepcontrol.wait` (`wait`) or `griddepcontrol.launch_dependents`. -/
  | gridDep (wait : Bool)
  deriving DecidableEq, Repr

namespace Decode

/-- The miscellaneous instruction of a recognized `createpolicy`, `nanosleep` or `pmevent`. -/
def MiscInstr.ofRaw (env : Env) (r : Isa.Raw) : M MiscInstr := do
  match r.entry with
  | .createpolicy_range =>
    return .createPolicy (← reg env 64 (← arg r "cache_policy")) (.range (flag r .space)
      (← MemAccess.addrOf env (← arg r "addr")) (← src env 32 (← arg r "primary_size"))
      (← src env 32 (← arg r "total_size")))
  | .createpolicy_fractional =>
    return .createPolicy (← reg env 64 (← arg r "cache_policy")) (.fraction none)
  | .createpolicy_fraction =>
    return .createPolicy (← reg env 64 (← arg r "cache_policy"))
      (.fraction (some (← src env 32 (← arg r "fraction"))))
  | .createpolicy_cvt =>
    return .createPolicy (← reg env 64 (← arg r "cache_policy"))
      (.cvt (← src env 64 (← arg r "access_property")))
  | .nanosleep => return .nanosleep (← src env 32 (← arg r "t"))
  | .pmevent =>
    let .literal t ← arg r "a" | throw "pmevent immediate"
    let .imm a ← literal t | throw "pmevent immediate"
    let mask := flag r .mask
    unless 0 ≤ a ∧ a < (if mask then 2 ^ 16 else 16) do throw "pmevent immediate out of range"
    return .pmevent mask a.toNat
  | .griddepcontrol => match r.get .action with
    | some .wait => return .gridDep true
    | some .launch_dependents => return .gridDep false
    | _ => throw "griddepcontrol action"
  | _ => throw "not a miscellaneous instruction"

end Decode

/-- The rule of a miscellaneous instruction: THREAD-CACHE-POLICY for `createpolicy`,
THREAD-NO-EFFECT for `nanosleep`, `pmevent` and `griddepcontrol`. -/
def MiscInstr.rule : MiscInstr → Option RuleId
  | .createPolicy .. => some .threadCachePolicy
  | .nanosleep _ | .pmevent .. | .gridDep _ => some .threadNoEffect

end PTX
