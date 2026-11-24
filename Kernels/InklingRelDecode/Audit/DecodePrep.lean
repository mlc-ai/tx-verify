-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public meta import Core.Source.Decode
public import Kernels.InklingRelDecode.Ptx
public meta import Kernels.InklingRelDecode.Ptx
public import Kernels.InklingRelDecode.Data.Decoded
public import Lemmas.Kernel.DecodeChunks
public import Tactics.KernelRfl
public meta import Lean.ToExpr
public meta import Lean.Elab.Command

@[expose] public section

/-! The decoding environment and the scope-resolved instruction list of the
InklingRelDecode kernel, as closed terms. `Decode.prepare` computes both from the
whole function; its kernel reduction resolves every nested scope and costs tens of
seconds, so the chunks of `decode_eq` decode against these terms instead. The terms
are written by evaluating `Decode.prepare` at elaboration time, and `DecodeHeader`
and `DecodeSource*` prove by kernel reduction that they are exactly what
`Decode.prepare` computes, so the evaluation is not trusted. -/

namespace PTX.Kernels.InklingRelDecode.DecodeAudit

open PTX PTX.Decode Lean

-- The generated name of the kernel function is longer than a line.
set_option linter.style.longLine false

/-- The kernel function of the frozen module. -/
abbrev source : Syntax.Function :=
  Generated.InklingRelDecode._rel_verify_kernel

meta section
deriving instance ToExpr for PTX.Syntax.Operand
deriving instance ToExpr for PTX.Decode.RegClass
deriving instance ToExpr for PTX.ParamObjectDecl
deriving instance ToExpr for PTX.Decode.Env
end

/-- The environment (`none`) or the instructions from index `a`, `n` of them (`some (a, n)`),
that the compiled decoder computes for `source`, as a term. -/
meta def preparedTerm (slice : Option (Nat × Nat)) : Elab.Term.TermElabM Expr := do
  match prepare Generated.InklingRelDecode.module.globals
    Generated.InklingRelDecode._rel_verify_kernel with
  | .error e => throwError "Decode.prepare failed: {e}"
  | .ok p => return match slice with
    | none => toExpr p.env
    | some (a, n) => toExpr ((p.instrs.drop a).take n)

elab "InklingRelDecode_prepared_env%" : term => preparedTerm none
elab "InklingRelDecode_prepared_instrs%" a:num n:num : term => preparedTerm (some (a.getNat, n.getNat))

set_option maxRecDepth 100000 in
/-- The decoding environment of `source`. -/
def env : Env := InklingRelDecode_prepared_env%

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 0, 714 of them. -/
def instrs0 : List SourceInstr := InklingRelDecode_prepared_instrs% 0 714

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 714, 714 of them. -/
def instrs1 : List SourceInstr := InklingRelDecode_prepared_instrs% 714 714

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 1428, 714 of them. -/
def instrs2 : List SourceInstr := InklingRelDecode_prepared_instrs% 1428 714

set_option maxRecDepth 100000 in
/-- The instructions of `source` from index 2142, 714 of them. -/
def instrs3 : List SourceInstr := InklingRelDecode_prepared_instrs% 2142 714

/-- The scope-resolved instructions of `source`, in source order. -/
def instrs : List SourceInstr := instrs0 ++ (instrs1 ++ (instrs2 ++ (instrs3)))

end PTX.Kernels.InklingRelDecode.DecodeAudit
