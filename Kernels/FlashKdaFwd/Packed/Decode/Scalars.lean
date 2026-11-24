-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Decode.Cache
public import Kernels.FlashKdaFwd.Packed.Decode.Names
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Prologue
open PTX PTX.Decode FlashKda.Packed.Transfers
set_option maxRecDepth 60000

private def token (wide : Bool) : Isa.Token := if wide then .b64 else .b32
def width (wide : Bool) : Nat := if wide then 64 else 32
private def opcode (wide : Bool) : String := if wide then "ld.param.b64" else "ld.param.b32"

private def rawLd (wide : Bool) (r n : String) : Isa.Raw :=
  ⟨.ld_param,[(.weak,none),(.space,some .param),(.type,some (token wide))],
    [⟨"d",.reg,.w,some (token wide),1,.register r⟩,⟨"a",.addr,.r,none,1,.address [.symbol n]⟩]⟩
def scalar (wide : Bool) (n : String) (d : Nat) : MemAccess :=
  {kind := .load, space := some .param, sem := .weak, elem := .int .b (width wide),
   addr := ⟨.param n false,0⟩, dsts := [some d]}
private theorem parseLd (wide : Bool) (pred : String → Bool) (r n : String) :
    Isa.Grammar.parse pred (opcode wide) [.register r,.address [.symbol n]] =
      .ok (rawLd wide r n) := by cases wide <;> kernel_rfl
private theorem lowerLd (wide : Bool) (e : Decode.Env) (r n : String) (d : Nat)
    (addr : Decode.MemAccess.addrOf e (.address [.symbol n]) = .ok ⟨.param n false,0⟩)
    (dst : Decode.MemAccess.loadDsts e (.int .b (width wide)) [.register r] =
      .ok ([some d], .same))
    (valid : Decode.MemAccess.paramChecks e (scalar wide n d) = .ok ()) :
    Decode.op e (opcode wide) [.register r,.address [.symbol n]] =
      .ok (.mem (scalar wide n d)) := by
  unfold Decode.op
  rw [parseLd]
  change ((fun a => match a with
    | some v => Op.mem v | none => .unmodeled (rawLd wide r n)) <$>
    Decode.MemAccess.ofRaw e (rawLd wide r n)) = _
  unfold Decode.MemAccess.ofRaw
  have entry : (rawLd wide r n).entry = .ld_param := rfl
  have space : (rawLd wide r n).get .space = some .param := rfl
  have sem : (rawLd wide r n).get .sem = none := rfl
  have weak : (rawLd wide r n).get .weak = none := rfl
  have scope : Decode.MemAccess.scope? ((rawLd wide r n).get .scope) = .ok none := rfl
  have dt : Decode.dtype ((rawLd wide r n).get .type) = .ok (.int .b (width wide)) := by
    cases wide <;> rfl
  have argA : Decode.arg (rawLd wide r n) "a" = .ok (.address [.symbol n]) := rfl
  have argD : Decode.args (rawLd wide r n) "d" = .ok [.register r] := rfl
  have policy : Decode.opnd? (rawLd wide r n) "cache_policy" = none := rfl
  have compare : Decode.opnd? (rawLd wide r n) "compare" = none := rfl
  have val : Decode.opnd? (rawLd wide r n) "value" = none := rfl
  have vec : (rawLd wide r n).get .vec = none := rfl
  simp only [entry, space, sem, weak, scope, dt, argA, argD, policy, compare, val, vec,
    MemAccess.space?, Option.map_some, addr, dst, pure, Except.pure, bind, Except.bind]
  simp only [ite_true, Bool.false_eq_true, ite_false]
  erw [valid]
  rfl

private def order : List (Fin 17) := [11,12,13,14,15,16,0,1,2,3,4,5,6,7,8,9,10]
private def bits (i : Fin 17) :=
  if i.val < 11 then 2048 else if i.val = 11 ∨ i.val = 15 then 64 else 32

private theorem table : env.params = order.map (fun i => (param i.val, bits i)) := by kernel_rfl

private theorem namedLookup (xs : List (Fin 17)) (i : Fin 17) :
    ((xs.map fun j => (param j.val, bits j)).lookup (param i.val)) =
      (xs.map fun j => (j, bits j)).lookup i := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    by_cases eq : i = j
    · subst j
      simp
    · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr eq,
        beq_eq_false_iff_ne.mpr (param_injective eq), ih]

private theorem noObject (j : Fin 17) (scalarArg : 11 ≤ j.val) :
    env.objects.find? (fun o => decide (o.name = param j.val)) = none := by
  have names : env.objects.map (·.name) = (List.range 11).map param := by kernel_rfl
  apply List.find?_eq_none.mpr
  intro o member h
  have hm : o.name ∈ env.objects.map (·.name) := List.mem_map_of_mem member
  rw [names] at hm
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp hm
  have lt := List.mem_range.mp hi
  have different : (⟨i, by omega⟩ : Fin 17) ≠ j := by
    intro e
    have hval : i = j.val := congrArg Fin.val e
    omega
  exact param_injective different (eq.trans (of_decide_eq_true h))

private theorem lookupWidth (j : Fin 17) :
    env.params.lookup (param j.val) = some (bits j) := by
  rw [table, namedLookup]
  exact (show ∀ i : Fin 17, (order.map fun k => (k,bits k)).lookup i = some (bits i)
    by decide +kernel) j

private theorem scalarOp (wide : Bool) (r : String) (d i : Nat) (j : Fin 17)
    (scalarArg : 11 ≤ j.val) (sameWidth : bits j = width wide)
    (dst : Decode.MemAccess.loadDsts env (.int .b (width wide)) [.register r] =
      .ok ([some d],.same))
    (sh : env.shared.lookup (param j.val) = none) :
    Decode.op {env with pc := i} (opcode wide) [.register r,.address [.symbol (param j.val)]] =
      .ok (.mem (scalar wide (param j.val) d)) := by
  have valid := lookupWidth j
  rw [sameWidth] at valid
  apply lowerLd
  · change MemAccess.addrOf env (.address [.symbol (param j.val)]) = _
    have loc : env.locals = [] := rfl
    have consts : env.consts = [] := rfl
    simp [MemAccess.addrOf, sh, loc, consts, noObject j scalarArg, valid, bind, Except.bind,
      pure, Except.pure]
  · exact dst
  · change MemAccess.paramChecks env (scalar wide (param j.val) d) = _
    cases wide <;> simp_all [MemAccess.paramChecks, scalar, width, DType.width,
      pure, Except.pure]

private theorem scalarSite (pc : Nat) (wide : Bool) (r : String) (j : Fin 17) (d : Nat)
    (scalarArg : 11 ≤ j.val) (sameWidth : bits j = width wide)
    (source : prepared.toOption.map (fun q => (q.instrs.drop pc).take 1) =
      some [(none,opcode wide,[.register r,Decode.resolveOperand topBindings
        (.address [.symbol (param j.val)])])])
    (dst : Decode.MemAccess.loadDsts env (.int .b (width wide)) [.register r] =
      .ok ([some d],.same)) (sh : env.shared.lookup (param j.val) = none) :
    slice pc 1 = some [⟨none,.mem (scalar wide (param j.val) d)⟩] := by
  have address : Decode.resolveOperand topBindings (.address [.symbol (param j.val)]) =
      .address [.symbol (param j.val)] := by
    change Syntax.Operand.address [Decode.resolveOperand topBindings (.symbol (param j.val))] = _
    rw [resolvedParam]
  rw [address] at source
  exact @checked pc 1 _ _ source
    (singleton_code (scalarOp wide r d pc j scalarArg sameWidth dst sh))

set_option maxHeartbeats 0 in
theorem readOffsets : slice 11 1 = some [⟨none,.mem (scalar true (param 15) 2262)⟩] :=
  scalarSite 11 true "%rd16" 15 2262 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

set_option maxHeartbeats 0 in
theorem readHeadCount : slice 320 1 = some [⟨none,.mem (scalar false (param 13) 2093)⟩] :=
  scalarSite 320 false "%r1787" 13 2093 (by decide) rfl
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end FlashKda.Packed.Prologue
