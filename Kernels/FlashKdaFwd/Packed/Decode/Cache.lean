-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Decode.Source
public meta import Kernels.FlashKdaFwd.Packed.Decode.Source
public import Tactics.KernelRfl
public meta import Lean.ToExpr
public meta import Lean.Elab.Command
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Transfers
open PTX

meta section
open Lean
deriving instance ToExpr for PTX.Syntax.Operand
deriving instance ToExpr for PTX.Decode.RegClass
deriving instance ToExpr for PTX.ParamObjectDecl
deriving instance ToExpr for PTX.Decode.Env

elab "packed_decode_env%" : term => do
  match prepared with
  | .ok p => return toExpr p.env
  | .error e => throwError "{e}"
end

set_option maxRecDepth 60000

def env : Decode.Env := packed_decode_env%

theorem env_eq : prepared.toOption.map (fun p => p.env) = some env := by kernel_rfl

private theorem checkedWindow {p : Option Decode.Prepared} {e : Decode.Env}
    {pc n : Nat} {xs : List Decode.SourceInstr} {ys : List Instr}
    (environment : p.map (·.env) = some e)
    (source : p.map (fun q => (q.instrs.drop pc).take n) = some xs)
    (code : Decode.code e pc xs = .ok ys) :
    (p.bind fun q => (Decode.code q.env pc ((q.instrs.drop pc).take n)).toOption) = some ys := by
  cases p with
  | none => cases environment
  | some q =>
    cases Option.some.inj environment
    cases Option.some.inj source
    exact congrArg Except.toOption code

theorem checked {pc n : Nat} {xs : List Decode.SourceInstr} {ys : List Instr}
    (source : prepared.toOption.map (fun q => (q.instrs.drop pc).take n) = some xs)
    (code : Decode.code env pc xs = .ok ys) : slice pc n = some ys :=
  checkedWindow env_eq source code

theorem singleton_code {env : Decode.Env} {pc : Nat} {args : List Syntax.Operand} {o : String}
    {op : Op}
    (h : Decode.op {env with pc := pc} o args = .ok op) :
    Decode.code env pc [(none,o,args)] = .ok [⟨none,op⟩] := by
  simp only [Decode.code, List.zipIdx_cons, List.zipIdx_nil, List.mapM_cons, List.mapM_nil,
    Decode.guard, bind, Except.bind, pure, Except.pure, h]

end FlashKda.Packed.Transfers
